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

/-- **Basic facts at a reduced-boundary point** (Steps 1 and 4 of the normal-average bounds in the
proof of Simon Ch. 3, Theorem 4.3; definition (4.2) of `∂*E`, `chapter-03.txt` lines 576–580, and
of `ν_E(x)` in 4.3, lines 588–596). If `x ∈ ∂*E`, then `x ∈ U` and the averages
`A(ρ) = μ(B_ρ(x))⁻¹ ∫_{B_ρ(x)} ν dμ` tend to some `v` with `|v| = 1` as `ρ ↓ 0`; by uniqueness
of limits along the nontrivial filter `𝓝[>] 0`, `ν_E(x) = limUnder A = v`. If `μ(B_ρ(x)) = 0`
for some `ρ > 0`, then `μ(B_r(x)) = 0` and `A(r) = 0⁻¹ • ∫ ν = 0` for `r ∈ (0, ρ)`, so `A → 0`
and `v = 0`, contradicting `|v| = 1`. -/
theorem Submission.deGiorgiNAB_reducedBoundary_basic : ∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), ∀ x ∈ reducedBoundary U μ ν, x ∈ U ∧ ‖reducedNormal μ ν x‖ = 1 ∧ Tendsto (normalAverage μ ν x) (𝓝[>] 0) (𝓝 (reducedNormal μ ν x)) ∧ ∀ ρ : ℝ, 0 < ρ → 0 < μ (Metric.ball x ρ) := by
  intro N U μ ν x hx
  -- Step 1: `x ∈ U` and `A → v` along `𝓝[>] 0` with `‖v‖ = 1`.
  obtain ⟨hxU, v, hv, hv1⟩ := hx
  -- Steps 2–3: `ν_E(x) = limUnder A = v` (`𝓝[>] 0` is nontrivial and `ℝᴺ` is Hausdorff).
  have he : reducedNormal μ ν x = v := hv.limUnder_eq
  refine ⟨hxU, he ▸ hv1, he ▸ hv, fun ρ hρ ↦ pos_iff_ne_zero.2 fun h0 ↦ ?_⟩
  -- Step 4: if `μ(B_ρ(x)) = 0`, then `A = 0` on `(0, ρ)`, so `v = 0`, contradicting `‖v‖ = 1`.
  have hA : normalAverage μ ν x =ᶠ[𝓝[>] 0] fun _ ↦ 0 := by
    filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
    rw [normalAverage, measure_mono_null (Metric.ball_subset_ball hr.2.le) h0,
      ENNReal.toReal_zero, inv_zero, zero_smul]
  have hv0 : v = 0 := tendsto_nhds_unique_of_eventuallyEq hv tendsto_const_nhds hA
  simp [hv0] at hv1
/-- **Cauchy–Schwarz bound for the normal excess on a set of finite measure** (Simon Ch. 3, proof
of Theorem 4.3, display (2)). Let `ν` be `μ`-a.e. strongly measurable with `|ν| = 1` `μ`-a.e., let
`|e| = 1`, and let `S ⊆ ℝᴺ` be any set with `μ(S) < ∞`; put `m = μ(S)` and `I = ∫_S ⟨ν, e⟩ dμ`.
Then `∫_S |ν − e| dμ ≤ m √(2(1 − m⁻¹ I))`. A.e. on `S`, `|ν − e|² = 2 − 2⟨ν, e⟩`, so
`∫_S |ν − e|² dμ = 2(m − I)`; with `J = ∫_S |ν − e| dμ`, expanding `0 ≤ ∫_S (|ν − e| − J/m)² dμ`
gives `J² ≤ 2m(m − I)` (Cauchy–Schwarz), and `√(2m(m − I)) = m √(2(1 − m⁻¹ I))` for `m > 0`. For
`m = 0` both sides vanish. -/
theorem Submission.deGiorgiNAB_excess_le_sqrt : ∀ (N : ℕ) (μ : Measure (Rn N)) (ν : Rn N → Rn N) (e : Rn N) (S : Set (Rn N)), μ S < ∞ → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ‖e‖ = 1 → ∫ y in S, ‖ν y - e‖ ∂μ ≤ (μ S).toReal * Real.sqrt (2 * (1 - (μ S).toReal⁻¹ * ∫ y in S, inner ℝ (ν y) e ∂μ)) := by
  intro N μ ν e S hS hν hν1 he
  -- Step 1: `μ ⌞ S` is a finite measure, for which `ν` is a.e. strongly measurable with `|ν| = 1`.
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hS.ne
  have hνS : ∀ᵐ y ∂(μ.restrict S), ‖ν y‖ = 1 := ae_restrict_of_ae hν1
  have hνm : AEStronglyMeasurable ν (μ.restrict S) := hν.restrict
  -- Step 2: `|ν − e| ≤ 2`, `|ν − e|² ≤ 4` and `|⟨ν, e⟩| ≤ 1` a.e., so all three are integrable.
  have hf_meas : AEStronglyMeasurable (fun y ↦ ‖ν y - e‖) (μ.restrict S) :=
    (hνm.sub aestronglyMeasurable_const).norm
  have hf_bd : ∀ᵐ y ∂(μ.restrict S), ‖ν y - e‖ ≤ 2 := by
    filter_upwards [hνS] with y hy
    calc ‖ν y - e‖ ≤ ‖ν y‖ + ‖e‖ := norm_sub_le _ _
      _ = 2 := by rw [hy, he]; norm_num
  have hf_int : Integrable (fun y ↦ ‖ν y - e‖) (μ.restrict S) := by
    refine Integrable.of_bound hf_meas 2 ?_
    filter_upwards [hf_bd] with y hy
    rwa [Real.norm_of_nonneg (norm_nonneg _)]
  have hf2_int : Integrable (fun y ↦ ‖ν y - e‖ ^ 2) (μ.restrict S) := by
    refine Integrable.of_bound (hf_meas.pow 2) 4 ?_
    filter_upwards [hf_bd] with y hy
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [norm_nonneg (ν y - e)]
  have hg_int : Integrable (fun y ↦ inner ℝ (ν y) e) (μ.restrict S) := by
    refine Integrable.of_bound ((continuous_id.inner continuous_const).comp_aestronglyMeasurable
      (g := fun v : Rn N ↦ inner ℝ v e) hνm) 1 ?_
    filter_upwards [hνS] with y hy
    calc ‖inner ℝ (ν y) e‖ ≤ ‖ν y‖ * ‖e‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hy, he]; norm_num
  set m := (μ S).toReal
  set I := ∫ y in S, inner ℝ (ν y) e ∂μ
  set J := ∫ y in S, ‖ν y - e‖ ∂μ
  have hreal : (μ.restrict S).real univ = m := by
    simp [measureReal_def, m]
  -- Step 3: a.e. `|ν − e|² = 2 − 2⟨ν, e⟩`, hence `∫_S |ν − e|² dμ = 2(m − I)`.
  have hK : ∫ y in S, ‖ν y - e‖ ^ 2 ∂μ = 2 * (m - I) := by
    have hae : (fun y ↦ ‖ν y - e‖ ^ 2) =ᵐ[μ.restrict S] fun y ↦ 2 - 2 * inner ℝ (ν y) e := by
      filter_upwards [hνS] with y hy
      rw [norm_sub_sq_real, hy, he]; ring
    rw [integral_congr_ae hae, integral_sub (integrable_const _) (hg_int.const_mul 2),
      integral_const_mul, integral_const, hreal, smul_eq_mul]
    ring
  have hJnn : 0 ≤ J := integral_nonneg fun y ↦ norm_nonneg _
  by_cases hm0 : m = 0
  · -- Step 4: `m = 0` forces `μ(S) = 0`, so `J = 0` and the right-hand side is `0`.
    have hS0 : μ S = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hm0 with h | h
      · exact h
      · exact absurd h hS.ne
    have hres : μ.restrict S = 0 := Measure.restrict_eq_zero.mpr hS0
    have hJ0 : J = 0 := by simp [J, hres]
    rw [hJ0, hm0, zero_mul]
  · have hmpos : 0 < m := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hm0)
    -- Step 5: `0 ≤ ∫_S (|ν − e| − J/m)² dμ = 2(m − I) − J²/m`, i.e. `J² ≤ m · 2(m − I)`.
    have hCS : J ^ 2 ≤ m * (2 * (m - I)) := by
      have h0 : 0 ≤ ∫ y in S, (‖ν y - e‖ - J / m) ^ 2 ∂μ := integral_nonneg fun y ↦ sq_nonneg _
      have hexp : ∫ y in S, (‖ν y - e‖ - J / m) ^ 2 ∂μ =
          2 * (m - I) - 2 * (J / m) * J + (J / m) ^ 2 * m := by
        have hfun : (fun y ↦ (‖ν y - e‖ - J / m) ^ 2) =
            fun y ↦ (‖ν y - e‖ ^ 2 - 2 * (J / m) * ‖ν y - e‖) + (J / m) ^ 2 := by
          ext y; ring
        have h1 : Integrable (fun y ↦ ‖ν y - e‖ ^ 2 - 2 * (J / m) * ‖ν y - e‖) (μ.restrict S) :=
          hf2_int.sub (hf_int.const_mul _)
        rw [hfun, integral_add h1 (integrable_const _),
          integral_sub hf2_int (hf_int.const_mul _), integral_const_mul, integral_const, hreal,
          hK, smul_eq_mul]
        ring
      rw [hexp] at h0
      have hJm : (J / m) ^ 2 * m = J ^ 2 / m := by field_simp
      have h2 : 2 * (J / m) * J = 2 * (J ^ 2 / m) := by field_simp
      rw [hJm, h2] at h0
      have h3 : J ^ 2 / m ≤ 2 * (m - I) := by linarith
      rwa [div_le_iff₀ hmpos, mul_comm] at h3
    -- Step 6: `J = √(J²) ≤ √(m² · 2(1 − m⁻¹ I)) = m √(2(1 − m⁻¹ I))`.
    calc J = Real.sqrt (J ^ 2) := (Real.sqrt_sq hJnn).symm
      _ ≤ Real.sqrt (m * (2 * (m - I))) := Real.sqrt_le_sqrt hCS
      _ = m * Real.sqrt (2 * (1 - m⁻¹ * I)) := by
        rw [show m * (2 * (m - I)) = m ^ 2 * (2 * (1 - m⁻¹ * I)) by field_simp,
          Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq hmpos.le]

/-- **Scalar normal averages at a reduced-boundary point** (Simon Ch. 3, proof of Theorem 4.3,
display (1), `chapter-03.txt` lines 607–614). Let `μ` be finite on compact subsets of the open set
`U`, `|ν| = 1` `μ`-a.e., `x ∈ ∂*E` and `e = ν_E(x)`. Then
`μ(B_ρ(x))⁻¹ ∫_{B_ρ(x)} ν · e dμ → 1` as `ρ ↓ 0` (with `0⁻¹ = 0`). For `ρ` below the radius of a
compact ball `B̄_r(x) ⊆ U`, `ν` is integrable on `B_ρ(x)`, so the functional `w ↦ e · w` commutes
with the integral and the scalar average is `A(ρ) · e` for `A(ρ) = normalAverage μ ν x ρ`; since
`A(ρ) → e` and `|e| = 1`, `A(ρ) · e → e · e = 1`. -/
theorem Submission.deGiorgiNAB_innerAverage_tendsto_one : ∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ∀ x ∈ reducedBoundary U μ ν, Tendsto (fun ρ : ℝ ↦ (μ (Metric.ball x ρ)).toReal⁻¹ * ∫ y in Metric.ball x ρ, inner ℝ (ν y) (reducedNormal μ ν x) ∂μ) (𝓝[>] 0) (𝓝 1) := by
  intro N U μ ν hU hfin hν hν1 x hx
  -- `x ∈ U`, `|e| = 1` and `A(ρ) → e`.
  obtain ⟨hxU, he, hA, -⟩ := Submission.deGiorgiNAB_reducedBoundary_basic N U μ ν x hx
  set e := reducedNormal μ ν x
  -- A compact ball `B̄_{ε/2}(x) ⊆ U`, so that `μ(B_ρ(x)) < ∞` for `ρ ≤ ε / 2`.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
  have hrU : Metric.closedBall x (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hfinr : μ (Metric.closedBall x (ε / 2)) < ∞ := hfin _ (isCompact_closedBall x _) hrU
  -- `A(ρ) · e → e · e = |e|² = 1`.
  have hlim : Tendsto (fun ρ ↦ inner ℝ (normalAverage μ ν x ρ) e) (𝓝[>] 0)
      (𝓝 (inner ℝ e e)) := hA.inner tendsto_const_nhds
  rw [real_inner_self_eq_norm_sq, he, one_pow] at hlim
  -- On `(0, ε / 2)` the scalar average equals `A(ρ) · e`.
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (half_pos hε)] with ρ hρ
  have hfinρ : μ (Metric.ball x ρ) < ∞ := (measure_mono (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall hρ.2.le))).trans_lt hfinr
  -- `ν` is integrable on `B_ρ(x)`: `|ν| ≤ 1` a.e. on a set of finite measure.
  have hint : IntegrableOn ν (Metric.ball x ρ) μ :=
    IntegrableOn.of_bound hfinρ hν.restrict 1 ((ae_restrict_of_ae hν1).mono fun y hy ↦ hy.le)
  -- The continuous linear functional `w ↦ e · w` commutes with the integral.
  have hcomm : ∫ y in Metric.ball x ρ, inner ℝ (ν y) e ∂μ =
      inner ℝ (∫ y in Metric.ball x ρ, ν y ∂μ) e := by
    simpa only [innerSL_apply_apply, real_inner_comm e] using
      (innerSL ℝ e).integral_comp_comm hint
  rw [normalAverage, real_inner_smul_left, hcomm]

/-- **Normal averages at a reduced-boundary point** (Simon Ch. 3, proof of Theorem 4.3, displays
(1) and (2), `chapter-03.txt` lines 604–620). Let `μ` be finite on compact subsets of the open set
`U`, `|ν| = 1` `μ`-a.e., `x ∈ ∂*E` and `e = ν_E(x)`. Then `|e| = 1`; there is `ρ₀ > 0` with
`B_{ρ₀}(x) ⊆ U` and `0 < μ(B_ρ(x)) ≤ 2 ∫_{B_ρ(x)} ν · e dμ` for `0 < ρ < ρ₀`; and if
`μ(B_ρ(x)) ≤ C ρⁿ` for small `ρ`, then `ρ⁻ⁿ ∫_{B_ρ(x)} |ν - e| dμ → 0` as `ρ ↓ 0`.
With `a(ρ) = μ(B_ρ(x))⁻¹ ∫_{B_ρ(x)} ν · e dμ`, (1) says `a(ρ) → 1`, so `a > 1/2` near `0`; and by
Cauchy–Schwarz (2), `∫_{B_ρ(x)} |ν - e| dμ ≤ μ(B_ρ(x)) √(2 (1 - a(ρ)))`, which is at most
`max(C, 0) ρⁿ √(2 (1 - a(ρ)))` and squeezes `ρ⁻ⁿ ∫_{B_ρ(x)} |ν - e| dμ` to `0`. -/
theorem Submission.deGiorgiDens_normalAverage_bounds : ∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen U → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ∀ x ∈ reducedBoundary U μ ν, ‖reducedNormal μ ν x‖ = 1 ∧ (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ Metric.ball x ρ₀ ⊆ U ∧ ∀ ρ ∈ Ioo 0 ρ₀, 0 < μ (Metric.ball x ρ) ∧ (μ (Metric.ball x ρ)).toReal ≤ 2 * ∫ y in Metric.ball x ρ, inner ℝ (ν y) (reducedNormal μ ν x) ∂μ) ∧ ∀ (n : ℕ) (C ρ₂ : ℝ), 0 < ρ₂ → (∀ ρ ∈ Ioo 0 ρ₂, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - reducedNormal μ ν x‖ ∂μ) (𝓝[>] 0) (𝓝 0) := by
  intro N U μ ν hU hfin hν hν1 x hx
  -- `x ∈ U`, `|e| = 1` and `μ(B_ρ(x)) > 0` for every `ρ > 0`; Simon (1): `a(ρ) → 1`.
  obtain ⟨hxU, he, -, hpos⟩ := Submission.deGiorgiNAB_reducedBoundary_basic N U μ ν x hx
  have ha := Submission.deGiorgiNAB_innerAverage_tendsto_one N U μ ν hU hfin hν hν1 x hx
  set e := reducedNormal μ ν x
  -- A compact ball `B̄_{ε/2}(x) ⊆ U`, so that `μ(B_ρ(x)) < ∞` for `ρ ≤ ε / 2`.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
  have hr : 0 < ε / 2 := half_pos hε
  have hrU : Metric.closedBall x (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hfinρ : ∀ ρ ≤ ε / 2, μ (Metric.ball x ρ) < ∞ := fun ρ hρ ↦
    (measure_mono (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hρ))).trans_lt (hfin _ (isCompact_closedBall x _) hrU)
  refine ⟨he, ?_, ?_⟩
  · -- `a > 1/2` on some `(0, δ)`; take `ρ₀ = min δ (ε / 2)`.
    obtain ⟨δ, hδ, hδa⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
      (ha.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1))
    refine ⟨min δ (ε / 2), lt_min hδ hr, (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (min_le_right _ _))).trans hrU,
      fun ρ hρ ↦ ⟨hpos ρ hρ.1, ?_⟩⟩
    have h12 : 1 / 2 <
        (μ (Metric.ball x ρ)).toReal⁻¹ * ∫ y in Metric.ball x ρ, inner ℝ (ν y) e ∂μ :=
      hδa ⟨hρ.1, hρ.2.trans_le (min_le_left _ _)⟩
    have hm : 0 < (μ (Metric.ball x ρ)).toReal :=
      ENNReal.toReal_pos (hpos ρ hρ.1).ne' (hfinρ ρ (hρ.2.le.trans (min_le_right _ _))).ne
    rw [lt_inv_mul_iff₀ hm] at h12
    linarith
  · -- Simon (2) and `μ(B_ρ(x)) ≤ max(C, 0) ρⁿ` squeeze the scaled excess to `0`.
    intro n C ρ₂ hρ₂ hmass
    have hup : Tendsto (fun ρ : ℝ ↦ max C 0 * Real.sqrt (2 * (1 - (μ (Metric.ball x ρ)).toReal⁻¹ *
        ∫ y in Metric.ball x ρ, inner ℝ (ν y) e ∂μ))) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous fun t : ℝ ↦ max C 0 * Real.sqrt (2 * (1 - t)) := by fun_prop
      exact (hc.tendsto' 1 0 (by simp)).comp ha
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hρ.le n)) (integral_nonneg fun y ↦ norm_nonneg _)
    · filter_upwards [Ioo_mem_nhdsGT (lt_min hρ₂ hr)] with ρ hρ
      have hρn : 0 < ρ ^ n := pow_pos hρ.1 n
      have hm : (μ (Metric.ball x ρ)).toReal ≤ max C 0 * ρ ^ n :=
        calc (μ (Metric.ball x ρ)).toReal ≤ (ENNReal.ofReal (C * ρ ^ n)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top
                (hmass ρ ⟨hρ.1, hρ.2.trans_le (min_le_left _ _)⟩)
          _ = max C 0 * ρ ^ n := by
              rw [ENNReal.toReal_ofReal', max_mul_of_nonneg _ _ hρn.le, zero_mul]
      have hB := Submission.deGiorgiNAB_excess_le_sqrt N μ ν e (Metric.ball x ρ)
        (hfinρ ρ (hρ.2.le.trans (min_le_right _ _))) hν hν1 he
      calc (ρ ^ n)⁻¹ * ∫ y in Metric.ball x ρ, ‖ν y - e‖ ∂μ
          ≤ (ρ ^ n)⁻¹ * (max C 0 * ρ ^ n * Real.sqrt (2 * (1 - (μ (Metric.ball x ρ)).toReal⁻¹ *
              ∫ y in Metric.ball x ρ, inner ℝ (ν y) e ∂μ))) :=
            mul_le_mul_of_nonneg_left
              (hB.trans (mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg _)))
              (inv_nonneg.mpr hρn.le)
        _ = max C 0 * Real.sqrt (2 * (1 - (μ (Metric.ball x ρ)).toReal⁻¹ *
              ∫ y in Metric.ball x ρ, inner ℝ (ν y) e ∂μ)) := by
            rw [mul_comm (max C 0), mul_assoc, inv_mul_cancel_left₀ hρn.ne']

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
