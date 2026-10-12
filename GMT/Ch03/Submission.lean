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

/-- **Density dichotomy** (Step 4 of the supplied proof of the sphere lemma in the
Besicovitch–Federer argument, Simon Ch. 3, Theorem 3.6; cf. Dall'Alba, Lemma 4.15 and
Theorem 4.16, and Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Ch. 18).
Let `σ` be a finite measure on `ℝᴺ` and `S ⊆ ℝᴺ` with `c₁ ρⁿ ≤ σ(B_ρ(ζ))` for `ζ ∈ S`,
`0 < ρ ≤ 2`, and `σ(B_ρ(ζ)) ≤ C₁ ρⁿ` for `ζ ∈ S`, `ρ > 0`. Let `m` be an outer measure and
`F ⊆ S` a Borel set with `m(F) = 0`. Then for `σ`-a.e. `θ ∈ F` either (α) `m(S ∩ B_t(θ)) = o(tⁿ)`
or (β) `m(S ∩ B_t(θ)) / tⁿ` is unbounded as `t ↓ 0`. By inner regularity `F` may be taken
closed. Then `Fⱼ = {θ ∈ F : m(S ∩ B_t(θ)) ≤ (j+1) tⁿ for 0 < t < 1/(j+1)}` is closed and
`m`-null, and covers the points of `F` where (β) fails. A Vitali covering of
`(S ∩ B_t(θ)) ∖ Fⱼ` by balls of radius `dist(·, Fⱼ)/2` and the lower bound give
`m(S ∩ B_t(θ)) ≤ ((j+1) 10ⁿ/c₁) σ(B̄_{2t}(θ) ∖ Fⱼ)`; at the `σ`-density points of `Fⱼ`
(Besicovitch) the upper bound turns this into (α). -/
theorem Submission.bf_sphereGood_densityDichotomy : ∀ (N n : ℕ) (σ : Measure (Rn N)), IsFiniteMeasure σ → ∀ (S : Set (Rn N)) (c₁ C₁ : ℝ), 0 < c₁ → (∀ ζ ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 2 → ENNReal.ofReal (c₁ * ρ ^ n) ≤ σ (Metric.ball ζ ρ)) → (∀ ζ ∈ S, ∀ ρ : ℝ, 0 < ρ → σ (Metric.ball ζ ρ) ≤ ENNReal.ofReal (C₁ * ρ ^ n)) → ∀ (m : OuterMeasure (Rn N)) (F : Set (Rn N)), MeasurableSet F → F ⊆ S → m F = 0 → σ {θ | θ ∈ F ∧ ¬ (∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η → m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (c * t ^ n)) ∧ ¬ (∀ K : ℝ, ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ t < η ∧ ENNReal.ofReal (K * t ^ n) < m (S ∩ Metric.ball θ t))} = 0 := by
  intro N n σ hσ S c₁ C₁ hc₁ hL hU m F hFm hFS hmF
  -- Step 3 (covering estimate): if `G` is closed and `m`-null and `m(S ∩ B_t(φ)) ≤ L tⁿ` for
  -- `φ ∈ G`, `0 < t < λ`, then `m(S ∩ B_t(θ)) ≤ (L 10ⁿ/c₁) σ(B̄_{2t}(θ) ∖ G)` for `θ ∈ G`,
  -- `0 < t ≤ 1` and `10 t < λ`.
  have hcover : ∀ G : Set (Rn N), IsClosed G → m G = 0 → ∀ L lam : ℝ, 0 ≤ L →
      (∀ φ ∈ G, ∀ t : ℝ, 0 < t → t < lam →
        m (S ∩ Metric.ball φ t) ≤ ENNReal.ofReal (L * t ^ n)) →
      ∀ θ ∈ G, ∀ t : ℝ, 0 < t → 10 * t < lam → t ≤ 1 →
        m (S ∩ Metric.ball θ t) ≤
          ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.closedBall θ (2 * t) \ G) := by
    intro G hG hmG L lam hL0 hGdef θ hθ t ht htlam ht1
    -- `R = (S ∩ B_t(θ)) ∖ G` carries all of the `m`-mass, as `m(G) = 0`.
    set R : Set (Rn N) := (S ∩ Metric.ball θ t) \ G
    have hmR : m (S ∩ Metric.ball θ t) ≤ m R :=
      calc m (S ∩ Metric.ball θ t) ≤ m (R ∪ G) := by
            refine measure_mono fun x hx ↦ ?_
            by_cases hxG : x ∈ G
            · exact Or.inr hxG
            · exact Or.inl ⟨hx, hxG⟩
        _ ≤ m R + m G := measure_union_le _ _
        _ = m R := by rw [hmG, add_zero]
    refine hmR.trans ?_
    have hGne : G.Nonempty := ⟨θ, hθ⟩
    -- (a) The radii `s_ζ = dist(ζ, G)/2` satisfy `0 < s_ζ < t/2` for `ζ ∈ R`.
    set s : Rn N → ℝ := fun ζ ↦ Metric.infDist ζ G / 2 with hs
    have hinf_pos : ∀ ζ ∈ R, 0 < Metric.infDist ζ G := fun ζ hζ ↦
      (hG.notMem_iff_infDist_pos hGne).1 hζ.2
    have hs_pos : ∀ ζ ∈ R, 0 < s ζ := fun ζ hζ ↦ half_pos (hinf_pos ζ hζ)
    have hs_lt : ∀ ζ ∈ R, s ζ < t / 2 := by
      intro ζ hζ
      have h1 : Metric.infDist ζ G ≤ dist ζ θ := Metric.infDist_le_dist_of_mem hθ
      have h2 : dist ζ θ < t := hζ.1.2
      simp only [hs]
      linarith
    -- (c), (d) Vitali: a disjoint, hence countable, subfamily `u` whose 5-fold enlargements
    -- cover `R`.
    obtain ⟨u, huR, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball R
      (fun ζ ↦ ζ) s (t / 2) (fun ζ hζ ↦ (hs_lt ζ hζ).le) 5 (by norm_num)
    have hu_count : u.Countable := hudisj.countable_of_isOpen (fun ζ _ ↦ Metric.isOpen_ball)
      (fun ζ hζ ↦ ⟨ζ, Metric.mem_ball_self (hs_pos ζ (huR hζ))⟩)
    have hRcov : R ⊆ ⋃ ζ ∈ u, S ∩ Metric.ball ζ (5 * s ζ) := by
      intro ζ hζ
      obtain ⟨ζ', hζ'u, hsub⟩ := hucov ζ hζ
      exact mem_biUnion hζ'u ⟨hζ.1.1, hsub (Metric.mem_ball_self (hs_pos ζ hζ))⟩
    -- (e) Each enlarged ball lies in a ball of radius `10 s_ζ` about some `φ ∈ G`, and the
    -- lower bound at `ζ ∈ S` controls `s_ζⁿ` by `σ(B_{s_ζ}(ζ))`.
    have hpiece : ∀ ζ ∈ u, m (S ∩ Metric.ball ζ (5 * s ζ)) ≤
        ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.ball ζ (s ζ)) := by
      intro ζ hζu
      have hζR := huR hζu
      have hsζ := hs_pos ζ hζR
      have hsζt := hs_lt ζ hζR
      have hinf := hinf_pos ζ hζR
      obtain ⟨φ, hφG, hφ⟩ : ∃ φ ∈ G, dist ζ φ < 5 * s ζ := by
        refine (Metric.infDist_lt_iff hGne).1 ?_
        simp only [hs]
        linarith
      have hball : Metric.ball ζ (5 * s ζ) ⊆ Metric.ball φ (10 * s ζ) :=
        Metric.ball_subset_ball' (by linarith)
      calc m (S ∩ Metric.ball ζ (5 * s ζ)) ≤ m (S ∩ Metric.ball φ (10 * s ζ)) :=
            measure_mono (inter_subset_inter_right _ hball)
        _ ≤ ENNReal.ofReal (L * (10 * s ζ) ^ n) := hGdef φ hφG _ (by positivity) (by linarith)
        _ = ENNReal.ofReal (L * 10 ^ n / c₁) * ENNReal.ofReal (c₁ * s ζ ^ n) := by
            rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hL0 (by positivity)) hc₁.le)]
            congr 1
            rw [mul_pow, div_mul_eq_mul_div, eq_div_iff hc₁.ne']
            ring
        _ ≤ ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.ball ζ (s ζ)) := by
            gcongr
            exact hL ζ hζR.1.1 _ hsζ (by linarith)
    -- (f) Countable subadditivity of `m`, additivity of `σ` on the disjoint balls, and (b):
    -- `B_{s_ζ}(ζ) ⊆ B̄_{2t}(θ) ∖ G`.
    calc m R ≤ m (⋃ ζ ∈ u, S ∩ Metric.ball ζ (5 * s ζ)) := measure_mono hRcov
      _ ≤ ∑' ζ : u, m (S ∩ Metric.ball ζ (5 * s ζ)) := measure_biUnion_le m hu_count _
      _ ≤ ∑' ζ : u, ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.ball ζ (s ζ)) :=
          ENNReal.tsum_le_tsum fun ζ ↦ hpiece ζ ζ.2
      _ = ENNReal.ofReal (L * 10 ^ n / c₁) * ∑' ζ : u, σ (Metric.ball ζ (s ζ)) :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (L * 10 ^ n / c₁) * σ (⋃ ζ ∈ u, Metric.ball ζ (s ζ)) := by
          rw [measure_biUnion hu_count hudisj fun _ _ ↦ measurableSet_ball]
      _ ≤ ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.closedBall θ (2 * t) \ G) := by
          gcongr
          intro x hx
          simp only [mem_iUnion] at hx
          obtain ⟨ζ, hζu, hxζ⟩ := hx
          have hζR := huR hζu
          have hsζt := hs_lt ζ hζR
          have hinf := hinf_pos ζ hζR
          rw [Metric.mem_ball] at hxζ
          refine ⟨?_, fun hxG ↦ ?_⟩
          · rw [Metric.mem_closedBall]
            have : dist ζ θ < t := hζR.1.2
            linarith [dist_triangle x ζ θ]
          · have h1 : Metric.infDist ζ G ≤ dist ζ x := Metric.infDist_le_dist_of_mem hxG
            rw [dist_comm] at h1
            simp only [hs] at hxζ
            linarith
  -- Step 4: with `G`, `L`, `λ` as in Step 3 and `G ⊆ S`, (α) holds at every `θ ∈ G` where the
  -- `σ`-density `q_θ(ρ) = σ(G ∩ B̄_ρ(θ)) / σ(B̄_ρ(θ))` tends to `1` as `ρ ↓ 0`.
  have halpha : ∀ G : Set (Rn N), IsClosed G → G ⊆ S → m G = 0 → ∀ L lam : ℝ, 0 ≤ L → 0 < lam →
      (∀ φ ∈ G, ∀ t : ℝ, 0 < t → t < lam →
        m (S ∩ Metric.ball φ t) ≤ ENNReal.ofReal (L * t ^ n)) →
      ∀ θ ∈ G, Tendsto (fun r ↦ σ (G ∩ Metric.closedBall θ r) / σ (Metric.closedBall θ r))
          (𝓝[>] 0) (𝓝 1) →
        ∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η →
          m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (c * t ^ n) := by
    intro G hG hGS hmG L lam hL0 hlam hGdef θ hθ hdens c hc
    have hθS : θ ∈ S := hGS hθ
    -- 0(b) Closed balls about `θ ∈ S` have positive, finite `σ`-measure.
    have hpos : ∀ ρ : ℝ, 0 < ρ → σ (Metric.closedBall θ ρ) ≠ 0 := by
      intro ρ hρ
      have h1 : ENNReal.ofReal (c₁ * (min ρ 2) ^ n) ≤ σ (Metric.ball θ (min ρ 2)) :=
        hL θ hθS _ (lt_min hρ two_pos) (min_le_right _ _)
      have h2 : σ (Metric.ball θ (min ρ 2)) ≤ σ (Metric.closedBall θ ρ) :=
        measure_mono ((Metric.ball_subset_ball (min_le_left _ _)).trans
          Metric.ball_subset_closedBall)
      have h3 : 0 < ENNReal.ofReal (c₁ * (min ρ 2) ^ n) :=
        ENNReal.ofReal_pos.2 (mul_pos hc₁ (pow_pos (lt_min hρ two_pos) n))
      exact (h3.trans_le (h1.trans h2)).ne'
    have hfin : ∀ ρ : ℝ, σ (Metric.closedBall θ ρ) ≠ ∞ := fun ρ ↦ measure_ne_top σ _
    -- (a), (c) `σ(B̄_{2t}(θ) ∖ G) / σ(B̄_{2t}(θ)) = 1 - q_θ(2t) → 0` as `t ↓ 0`.
    have h2t : Tendsto (fun t : ℝ ↦ 2 * t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 0) (𝓝 (2 * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos two_pos (show (0 : ℝ) < t from ht)
    have hq := hdens.comp h2t
    have hf : Tendsto (fun t : ℝ ↦ σ (Metric.closedBall θ (2 * t) \ G) /
        σ (Metric.closedBall θ (2 * t))) (𝓝[>] 0) (𝓝 0) := by
      have hsub := ENNReal.Tendsto.sub tendsto_const_nhds hq (Or.inl ENNReal.one_ne_top)
      rw [tsub_self] at hsub
      refine hsub.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      simp only [Function.comp_apply]
      have hρ : 0 < 2 * t := mul_pos two_pos ht
      have hadd := measure_inter_add_sdiff (μ := σ) (Metric.closedBall θ (2 * t)) hG.measurableSet
      have hdiff : σ (Metric.closedBall θ (2 * t) \ G) =
          σ (Metric.closedBall θ (2 * t)) - σ (Metric.closedBall θ (2 * t) ∩ G) :=
        ENNReal.eq_sub_of_add_eq (measure_ne_top σ _) (by rw [add_comm]; exact hadd)
      rw [hdiff, ENNReal.sub_div (fun _ _ ↦ hpos _ hρ), ENNReal.div_self (hpos _ hρ) (hfin _),
        inter_comm]
    -- (b) With `M = (L 10ⁿ/c₁) C₁ 4ⁿ`, Step 3 and the upper bound at radius `4t` give
    -- `m(S ∩ B_t(θ)) ≤ tⁿ · M · σ(B̄_{2t}(θ) ∖ G) / σ(B̄_{2t}(θ))`; choose `η` from (c).
    obtain ⟨M, hM⟩ : ∃ M : ℝ≥0∞,
        M = ENNReal.ofReal (L * 10 ^ n / c₁) * ENNReal.ofReal (C₁ * 4 ^ n) := ⟨_, rfl⟩
    have hMf : M ≠ ∞ := by
      rw [hM]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hMf' : Tendsto (fun t : ℝ ↦ M * (σ (Metric.closedBall θ (2 * t) \ G) /
        σ (Metric.closedBall θ (2 * t)))) (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hf (Or.inr hMf)
      rwa [mul_zero] at this
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), M * (σ (Metric.closedBall θ (2 * t) \ G) /
        σ (Metric.closedBall θ (2 * t))) < ENNReal.ofReal c :=
      hMf'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hc))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine ⟨min u (min (lam / 10) 1), lt_min hu (lt_min (by positivity) one_pos),
      fun t ht htη ↦ ?_⟩
    have htu : t < u := htη.trans_le (min_le_left _ _)
    have htlam : 10 * t < lam := by
      have := htη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      linarith
    have ht1 : t ≤ 1 := (htη.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
    have hρ : 0 < 2 * t := mul_pos two_pos ht
    have hlt : M * (σ (Metric.closedBall θ (2 * t) \ G) / σ (Metric.closedBall θ (2 * t))) <
        ENNReal.ofReal c := hsub ⟨ht, htu⟩
    have hball : σ (Metric.closedBall θ (2 * t)) ≤
        ENNReal.ofReal (C₁ * 4 ^ n) * ENNReal.ofReal (t ^ n) := by
      calc σ (Metric.closedBall θ (2 * t)) ≤ σ (Metric.ball θ (4 * t)) :=
            measure_mono (Metric.closedBall_subset_ball (by linarith))
        _ ≤ ENNReal.ofReal (C₁ * (4 * t) ^ n) := hU θ hθS _ (by positivity)
        _ = ENNReal.ofReal (C₁ * 4 ^ n) * ENNReal.ofReal (t ^ n) := by
            rw [mul_pow, ← mul_assoc, ENNReal.ofReal_mul' (by positivity)]
    calc m (S ∩ Metric.ball θ t)
        ≤ ENNReal.ofReal (L * 10 ^ n / c₁) * σ (Metric.closedBall θ (2 * t) \ G) :=
          hcover G hG hmG L lam hL0 hGdef θ hθ t ht htlam ht1
      _ = ENNReal.ofReal (L * 10 ^ n / c₁) * (σ (Metric.closedBall θ (2 * t)) *
            (σ (Metric.closedBall θ (2 * t) \ G) / σ (Metric.closedBall θ (2 * t)))) := by
          rw [ENNReal.mul_div_cancel (hpos _ hρ) (hfin _)]
      _ ≤ ENNReal.ofReal (L * 10 ^ n / c₁) * ((ENNReal.ofReal (C₁ * 4 ^ n) *
            ENNReal.ofReal (t ^ n)) * (σ (Metric.closedBall θ (2 * t) \ G) /
              σ (Metric.closedBall θ (2 * t)))) := by
          gcongr
      _ = ENNReal.ofReal (t ^ n) * (M * (σ (Metric.closedBall θ (2 * t) \ G) /
            σ (Metric.closedBall θ (2 * t)))) := by
          rw [hM]
          ring
      _ ≤ ENNReal.ofReal (t ^ n) * ENNReal.ofReal c := mul_le_mul' le_rfl hlt.le
      _ = ENNReal.ofReal (c * t ^ n) := by
          rw [ENNReal.ofReal_mul' (pow_nonneg ht.le n), mul_comm]
  -- Steps 2 and 5: the statement for a closed `F' ⊆ S` with `m(F') = 0`.
  have hclosed : ∀ F' : Set (Rn N), IsClosed F' → F' ⊆ S → m F' = 0 →
      σ {θ | θ ∈ F' ∧ ¬ (∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η →
          m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (c * t ^ n)) ∧
        ¬ (∀ K : ℝ, ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ t < η ∧
          ENNReal.ofReal (K * t ^ n) < m (S ∩ Metric.ball θ t))} = 0 := by
    intro F' hFc hF'S hmF'
    -- Step 2: `F'ⱼ = {θ ∈ F' : m(S ∩ B_t(θ)) ≤ (j+1) tⁿ for 0 < t < 1/(j+1)}`.
    let Fj : ℕ → Set (Rn N) := fun j ↦ {θ | θ ∈ F' ∧ ∀ t : ℝ, 0 < t → t < 1 / ((j : ℝ) + 1) →
      m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (((j : ℝ) + 1) * t ^ n)}
    have hFjF : ∀ j, Fj j ⊆ F' := fun j θ hθ ↦ hθ.1
    -- (b) `F'ⱼ` is closed: `B_t(θ) ⊆ B_{t+τ}(θ')` for `θ' ∈ F'ⱼ` near `θ`; let `τ ↓ 0`.
    have hFjc : ∀ j, IsClosed (Fj j) := by
      intro j
      rw [← closure_subset_iff_isClosed]
      intro θ hθ
      have hθF : θ ∈ F' := hFc.closure_subset_iff.2 (hFjF j) hθ
      refine ⟨hθF, fun t ht htj ↦ ?_⟩
      have key : ∀ τ ∈ Ioo (0 : ℝ) (1 / ((j : ℝ) + 1) - t),
          m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (((j : ℝ) + 1) * (t + τ) ^ n) := by
        rintro τ ⟨hτ, hτ'⟩
        obtain ⟨θ', hθ', hd⟩ := Metric.mem_closure_iff.1 hθ τ hτ
        calc m (S ∩ Metric.ball θ t) ≤ m (S ∩ Metric.ball θ' (t + τ)) :=
              measure_mono (inter_subset_inter_right _ (Metric.ball_subset_ball' (by linarith)))
          _ ≤ _ := hθ'.2 (t + τ) (by linarith) (by linarith)
      have hcont : Tendsto (fun τ : ℝ ↦ ENNReal.ofReal (((j : ℝ) + 1) * (t + τ) ^ n)) (𝓝[>] 0)
          (𝓝 (ENNReal.ofReal (((j : ℝ) + 1) * t ^ n))) := by
        have h : Continuous fun τ : ℝ ↦ ENNReal.ofReal (((j : ℝ) + 1) * (t + τ) ^ n) :=
          ENNReal.continuous_ofReal.comp
            (continuous_const.mul ((continuous_const.add continuous_id).pow n))
        have := h.tendsto 0
        simp only [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact ge_of_tendsto hcont (mem_of_superset (Ioo_mem_nhdsGT
        (by linarith : (0 : ℝ) < 1 / ((j : ℝ) + 1) - t)) fun τ hτ ↦ key τ hτ)
    -- (a) `m(F'ⱼ) ≤ m(F') = 0`.
    have hmFj : ∀ j, m (Fj j) = 0 := fun j ↦ measure_mono_null (hFjF j) hmF'
    -- (c) A point of `F'` where (β) fails lies in some `F'ⱼ`.
    have hβ : ∀ θ ∈ F', ¬ (∀ K : ℝ, ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ t < η ∧
        ENNReal.ofReal (K * t ^ n) < m (S ∩ Metric.ball θ t)) → ∃ j, θ ∈ Fj j := by
      intro θ hθ hnβ
      push Not at hnβ
      obtain ⟨K, η, hη, hK⟩ := hnβ
      obtain ⟨j, hj⟩ := exists_nat_ge (max K (1 / η))
      refine ⟨j, hθ, fun t ht htj ↦ ?_⟩
      have hjK : K ≤ (j : ℝ) + 1 := by linarith [le_max_left K (1 / η)]
      have hjη : 1 / ((j : ℝ) + 1) ≤ η := by
        rw [div_le_iff₀ (by positivity)]
        have : 1 / η ≤ j := (le_max_right _ _).trans hj
        rw [div_le_iff₀ hη] at this
        nlinarith
      calc m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (K * t ^ n) := hK t ht (by linarith)
        _ ≤ ENNReal.ofReal (((j : ℝ) + 1) * t ^ n) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hjK (by positivity))
    -- Step 4 with the Besicovitch density theorem: (α) fails only on a `σ`-null part of `F'ⱼ`.
    have hnull : ∀ j, σ {θ | θ ∈ Fj j ∧ ¬ (∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t →
        t < η → m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (c * t ^ n))} = 0 := by
      intro j
      have h := Besicovitch.ae_tendsto_measure_inter_div σ (Fj j)
      rw [ae_restrict_iff' (hFjc j).measurableSet, ae_iff] at h
      refine measure_mono_null ?_ h
      rintro θ ⟨hθ, hnα⟩ hall
      exact hnα (halpha (Fj j) (hFjc j) ((hFjF j).trans hF'S) (hmFj j) ((j : ℝ) + 1)
        (1 / ((j : ℝ) + 1)) (by positivity) (by positivity) (fun φ hφ ↦ hφ.2) θ hθ (hall hθ))
    -- Step 5: the exceptional set lies in `⋃ⱼ {θ ∈ F'ⱼ : (α) fails at θ}`.
    refine measure_mono_null ?_ (measure_iUnion_null hnull)
    rintro θ ⟨hθF, hnα, hnβ⟩
    obtain ⟨j, hj⟩ := hβ θ hθF hnβ
    exact mem_iUnion.2 ⟨j, hj, hnα⟩
  -- Step 1: reduction to closed sets. Inner regularity gives closed `Fₖ ⊆ F` with
  -- `σ(F ∖ Fₖ) < 1/k`, and the exceptional set lies in `(F ∖ ⋃ₖ Fₖ) ∪ ⋃ₖ Exc(Fₖ)`.
  have happrox : ∀ k : ℕ, ∃ Fk, Fk ⊆ F ∧ IsClosed Fk ∧ σ (F \ Fk) < (k : ℝ≥0∞)⁻¹ := fun k ↦
    hFm.exists_isClosed_sdiff_lt (measure_ne_top σ F) (by simp)
  choose Fk hFkF hFkc hFkσ using happrox
  have hD : σ (F \ ⋃ k, Fk k) = 0 := by
    refine le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun k ↦ ?_) zero_le
    exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion Fk k))).trans (hFkσ k).le
  refine measure_mono_null ?_ (measure_union_null hD (measure_iUnion_null fun k ↦
    hclosed (Fk k) (hFkc k) ((hFkF k).trans hFS) (measure_mono_null (hFkF k) hmF)))
  rintro θ ⟨hθF, hnα, hnβ⟩
  by_cases h : θ ∈ ⋃ k, Fk k
  · obtain ⟨k, hk⟩ := mem_iUnion.1 h
    exact Or.inr (mem_iUnion.2 ⟨k, hk, hnα, hnβ⟩)
  · exact Or.inl ⟨hθF, h⟩

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
