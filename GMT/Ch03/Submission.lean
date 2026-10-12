import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter02.BV
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter02.WeightedArea

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

/-- **Slice integrals over a `C¹` chart** (steps 1–3 of the supplied proof of the chart formula
for the `C¹` parametric co-area formula, Simon Ch. 3, (2.8)–(2.9)). Let `Φ` be an open partial
homeomorphism from `ℝ^{m+k}` to `ℝᵐ × ℝᵏ` (Euclidean product) whose first component is `G` and
whose inverse is `C¹`, let `ψ` be `C¹` and injective on `Φ.source`, and let `B ⊆ Φ.source` be
Borel. If the injective area formula (AF) holds for `φ` in dimension `k`, then for every `y ∈ ℝᵐ`,
`∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ = ∫_{ℝᵏ} F(y, z) dz` with `F = 1_{Φ(B)} · φ ∘ ψ ∘ Φ⁻¹ ·
normDet(D(ψ ∘ Φ⁻¹) ∘ j)`, `j z = (0, z)`: apply (AF) to `χ = ψ ∘ Φ⁻¹ ∘ ι`, `ι z = (y, z)`, on the
Borel set `S = ι⁻¹(Φ(B))`, whose image is `ψ(B ∩ G⁻¹{y})`, and use `Dχ(z) = D(ψ ∘ Φ⁻¹)(ι z) ∘ j`. -/
theorem Submission.pcoarea_chart_slice_lintegral : ∀ (m k N : ℕ) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m) (Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k))), ContDiffOn ℝ 1 ψ Φ.source → InjOn ψ Φ.source → ContDiffOn ℝ 1 Φ.symm Φ.target → (∀ u ∈ Φ.source, (Φ u).fst = G u) → ∀ B ⊆ Φ.source, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, (∀ (V : Set (Rn k)) (χ : Rn k → Rn N), IsOpen V → ContDiffOn ℝ 1 χ V → InjOn χ V → ∀ S ⊆ V, MeasurableSet S → ∫⁻ x in χ '' S, φ x ∂μHE[k] = ∫⁻ z in S, φ (χ z) * ENNReal.ofReal ((fderiv ℝ χ z).toLinearMap.normDet)) → ∀ y : Rn m, ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k] = ∫⁻ z : Rn k, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) (WithLp.toLp 2 (y, z)) := by
  intro m k N ψ G Φ hψ hinj hΦs hfst B hB hBm φ hAF y
  classical
  -- Step 1: the slice map `ι z = (y, z)` has derivative `j z = (0, z)`, is `C¹` and injective.
  set j : Rn k →L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (Rn m) (Rn k))
  let ι : Rn k → WithLp 2 (Rn m × Rn k) := fun z ↦ WithLp.toLp 2 (y, z)
  have hιd : ∀ z, HasFDerivAt ι j z := by
    intro z
    have h1 : HasFDerivAt (fun z : Rn k ↦ (y, z)) (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)) z :=
      hasFDerivAt_prodMk_right y z
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.hasFDerivAt.comp z h1
  have hιcd : ContDiff ℝ 1 ι :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.contDiff.comp
      (contDiff_const.prodMk contDiff_id)
  have hιc : Continuous ι := hιcd.continuous
  have hιinj : Function.Injective ι := by
    intro z₁ z₂ h
    simpa [ι] using congrArg WithLp.snd h
  -- Step 2: `Φ(B)` is a Borel subset of `Φ.target` (Lusin–Souslin).
  have hB' : MeasurableSet (Φ '' B) :=
    hBm.image_of_continuousOn_injOn (Φ.continuousOn.mono hB) (Φ.injOn.mono hB)
  have hB'Ω : Φ '' B ⊆ Φ.target := by
    rintro _ ⟨u, hu, rfl⟩
    exact Φ.map_source (hB hu)
  -- Step 3: `V = ι⁻¹(Φ.target)` is open and `S = ι⁻¹(Φ(B)) ⊆ V` is Borel.
  have hV : IsOpen (ι ⁻¹' Φ.target) := Φ.open_target.preimage hιc
  have hS : MeasurableSet (ι ⁻¹' (Φ '' B)) := hιc.measurable hB'
  have hSV : ι ⁻¹' (Φ '' B) ⊆ ι ⁻¹' Φ.target := fun z hz ↦ hB'Ω hz
  -- Steps 4–5: `χ = ψ ∘ Φ⁻¹ ∘ ι` is `C¹` and injective on `V`.
  let χ : Rn k → Rn N := fun z ↦ ψ (Φ.symm (ι z))
  have hχ : ContDiffOn ℝ 1 χ (ι ⁻¹' Φ.target) := by
    have h1 : ContDiffOn ℝ 1 (fun z ↦ Φ.symm (ι z)) (ι ⁻¹' Φ.target) :=
      hΦs.comp hιcd.contDiffOn (fun z hz ↦ hz)
    exact hψ.comp h1 (fun z hz ↦ Φ.map_target hz)
  have hχi : InjOn χ (ι ⁻¹' Φ.target) := by
    intro z₁ h₁ z₂ h₂ h
    exact hιinj (Φ.symm.injOn h₁ h₂ (hinj (Φ.map_target h₁) (Φ.map_target h₂) h))
  -- Step 6: `ψ(B ∩ G⁻¹{y}) = χ(S)`, since `ι((Φ u).snd) = Φ u` when `G u = y`.
  have himg : ψ '' (B ∩ G ⁻¹' {y}) = χ '' (ι ⁻¹' (Φ '' B)) := by
    ext x
    constructor
    · rintro ⟨u, ⟨huB, huG⟩, rfl⟩
      have hfu : (Φ u).fst = y := (hfst u (hB huB)).trans huG
      have hιu : ι (Φ u).snd = Φ u := by
        show WithLp.toLp 2 (y, (Φ u).snd) = Φ u
        rw [← hfu]
        rfl
      refine ⟨(Φ u).snd, ?_, ?_⟩
      · show ι (Φ u).snd ∈ Φ '' B
        rw [hιu]
        exact ⟨u, huB, rfl⟩
      · show ψ (Φ.symm (ι (Φ u).snd)) = ψ u
        rw [hιu, Φ.left_inv (hB huB)]
    · rintro ⟨z, ⟨u, huB, hu⟩, rfl⟩
      refine ⟨u, ⟨huB, ?_⟩, ?_⟩
      · show G u = y
        rw [← hfst u (hB huB), hu]
        rfl
      · show ψ u = ψ (Φ.symm (ι z))
        rw [← hu, Φ.left_inv (hB huB)]
  -- Step 8: chain rule on `V`, `Dχ(z) = D(ψ ∘ Φ⁻¹)(ι z) ∘ j`.
  have hderiv : ∀ z ∈ ι ⁻¹' Φ.target, fderiv ℝ χ z = (fderiv ℝ (ψ ∘ Φ.symm) (ι z)).comp j := by
    intro z hz
    have hΦsd : DifferentiableAt ℝ Φ.symm (ι z) :=
      (hΦs.differentiableOn one_ne_zero _ hz).differentiableAt (Φ.open_target.mem_nhds hz)
    have hψd : DifferentiableAt ℝ ψ (Φ.symm (ι z)) :=
      (hψ.differentiableOn one_ne_zero _ (Φ.map_target hz)).differentiableAt
        (Φ.open_source.mem_nhds (Φ.map_target hz))
    have hχeq : χ = (ψ ∘ Φ.symm) ∘ ι := rfl
    rw [hχeq, fderiv_comp z (hψd.comp (ι z) hΦsd) (hιd z).differentiableAt, (hιd z).fderiv]
  -- Steps 7, 9, 10: apply (AF) on `(V, χ, S)` and compare the integrands pointwise.
  rw [himg, hAF (ι ⁻¹' Φ.target) χ hV hχ hχi (ι ⁻¹' (Φ '' B)) hSV hS, ← lintegral_indicator hS]
  refine lintegral_congr fun z ↦ ?_
  by_cases hz : z ∈ ι ⁻¹' (Φ '' B)
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show WithLp.toLp 2 (y, z) ∈ Φ '' B from hz),
      hderiv z (hSV hz)]
  · rw [Set.indicator_of_notMem hz,
      Set.indicator_of_notMem (show WithLp.toLp 2 (y, z) ∉ Φ '' B from hz)]

/-- **Chart integrand of the parametric co-area formula: Borel measurability and Tonelli.**
Let `Φ` be an open partial homeomorphism from `ℝⁿ`, `n = m + k`, onto an open subset `Ω` of the
Euclidean product `P = WithLp 2 (ℝᵐ × ℝᵏ)`, let `ψ` be continuous on `O = Φ.source`, `B ⊆ O` Borel
and `φ ≥ 0` Borel. With `ρ = ψ ∘ Φ⁻¹` and `j z = toLp (0, z)`, the function
`F = 1_{Φ(B)} · (φ ∘ ρ) · normDet (Dρ ∘ j)` on `P` is Borel: `Φ(B)` is Borel by Lusin–Souslin
(`Φ` is continuous and injective on `O`), `ρ` agrees on `Φ(B)` with the Borel map
`Ω.piecewise ρ 0`, `w ↦ Dρ(w)` is Borel for every `ρ` (`measurable_fderiv`) and
`normDet M = √det (M† M)` is continuous in `M`. Since `toLp` carries `Lᵐ ⊗ Lᵏ` to the volume of
`P`, Tonelli's theorem gives that `y ↦ ∫ F(toLp (y, z)) dLᵏ(z)` is Borel and
`∫_P F = ∫_{ℝᵐ} ∫_{ℝᵏ} F(toLp (y, z)) dLᵏ(z) dLᵐ(y)`. No differentiability is assumed. -/
theorem Submission.pcoarea_chart_integrand_tonelli : ∀ (m k N : ℕ) (ψ : Rn (m + k) → Rn N) (Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k))), ContinuousOn ψ Φ.source → ∀ B ⊆ Φ.source, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → Measurable (fun y : Rn m ↦ ∫⁻ z : Rn k, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) (WithLp.toLp 2 (y, z))) ∧ ∫⁻ w, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) w = ∫⁻ y : Rn m, ∫⁻ z : Rn k, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) (WithLp.toLp 2 (y, z)) := by
  intro m k N ψ Φ hψ B hB hBm φ hφ
  classical
  set j : Rn k →L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (Rn m) (Rn k))
  -- Step 1: `Φ(B)` is Borel (Lusin–Souslin) and lies in `Ω = Φ.target`.
  have hB' : MeasurableSet (Φ '' B) :=
    hBm.image_of_continuousOn_injOn (Φ.continuousOn.mono hB) (Φ.injOn.mono hB)
  have hB'Ω : Φ '' B ⊆ Φ.target := by
    rintro _ ⟨u, hu, rfl⟩
    exact Φ.map_source (hB hu)
  -- Step 2: `ρ = ψ ∘ Φ⁻¹` is continuous on the open set `Ω`, so `Ω.piecewise ρ 0` is Borel.
  have hρ : ContinuousOn (ψ ∘ Φ.symm) Φ.target :=
    hψ.comp Φ.continuousOn_symm (fun w hw ↦ Φ.map_target hw)
  have hρm : Measurable (Φ.target.piecewise (ψ ∘ Φ.symm) (fun _ ↦ 0)) :=
    hρ.measurable_piecewise continuousOn_const Φ.open_target.measurableSet
  -- Step 3: `normDet M = √det (M† M)` is continuous, so the Jacobian factor is Borel.
  have hnd : Continuous (fun M : Rn k →L[ℝ] Rn N ↦ M.toLinearMap.normDet) := by
    have heq : (fun M : Rn k →L[ℝ] Rn N ↦ M.toLinearMap.normDet) =
        fun M ↦ Real.sqrt ((M.adjoint ∘L M).det) := by
      funext M
      rw [← M.normDet_sq]
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using (Real.sqrt_sq M.normDet_nonneg).symm
    rw [heq]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  have ha : Measurable
      (fun w ↦ ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) :=
    ENNReal.measurable_ofReal.comp
      ((hnd.comp (continuous_id.clm_comp continuous_const)).measurable.comp (measurable_fderiv ℝ _))
  -- Step 4: on `Φ(B)` the integrand agrees with a Borel function, so it is Borel.
  have hFeq : (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) *
        ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) =
      (Φ '' B).indicator (fun w ↦ φ (Φ.target.piecewise (ψ ∘ Φ.symm) (fun _ ↦ 0) w) *
        ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) := by
    apply Set.indicator_congr
    intro w hw
    simp only [Set.piecewise_eq_of_mem _ _ _ (hB'Ω hw), Function.comp_apply]
  have hFm : Measurable ((Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) *
      ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet))) := by
    rw [hFeq]
    exact ((hφ.comp hρm).mul ha).indicator hB'
  -- Step 5: transport along the measure-preserving `toLp` and apply Tonelli on `ℝᵐ × ℝᵏ`.
  have hmp := WithLp.volume_preserving_toLp (Rn m) (Rn k)
  have hFp := hFm.comp (WithLp.measurable_toLp 2 (Rn m × Rn k))
  refine ⟨hFp.lintegral_prod_right', ?_⟩
  rw [← hmp.lintegral_comp hFm, Measure.volume_eq_prod]
  exact lintegral_prod _ hFp.aemeasurable
/-- **Change of variables from `ℝⁿ` into `P = WithLp 2 (ℝᵐ × ℝᵏ)`** (`n = m + k`; Simon Ch. 3,
(2.8)–(2.9), `chapter-03.txt` lines 412–436, via the `C¹` co-area formula Ch. 2 (6.3),
`chapter-02.txt` lines 1462–1476, whose proof Simon omits; this is the injective
equal-dimensional case of the area formula Ch. 2 (3.1)–(3.5), `chapter-02.txt` lines 743–797):
if `f : ℝⁿ → P` has derivative `f'(u)` within the Borel set `B` at every `u ∈ B` and is injective
on `B`, then `∫_{f(B)} g = ∫_B normDet(f'(u)) · g(f(u)) du` for every `g : P → [0, ∞]`.
As `finrank P = n`, there is a linear isometric equivalence `e : P ≃ ℝⁿ`; `e⁻¹` preserves volume,
Mathlib's change of variables applies to `e ∘ f` on `B`, and
`|det(e ∘ f'(u))| = normDet(e) · normDet(f'(u)) = normDet(f'(u))`. -/
theorem Submission.pcoarea_chart_change_of_variables : ∀ (m k : ℕ) (f : Rn (m + k) → WithLp 2 (Rn m × Rn k)) (f' : Rn (m + k) → Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) (B : Set (Rn (m + k))), MeasurableSet B → (∀ u ∈ B, HasFDerivWithinAt f (f' u) B u) → InjOn f B → ∀ g : WithLp 2 (Rn m × Rn k) → ℝ≥0∞, ∫⁻ w in f '' B, g w = ∫⁻ u in B, ENNReal.ofReal ((f' u).toLinearMap.normDet) * g (f u) := by
  intro m k f f' B hB hf hinj g
  -- Step 1: `finrank P = m + k`.
  have hfin : finrank ℝ (WithLp 2 (Rn m × Rn k)) = m + k := by
    rw [(WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).finrank_eq, Module.finrank_prod]
    simp
  -- Step 2: a linear isometric equivalence `e : P ≃ ℝⁿ`, and `E = e` as a continuous linear map.
  let e : WithLp 2 (Rn m × Rn k) ≃ₗᵢ[ℝ] Rn (m + k) :=
    ((stdOrthonormalBasis ℝ (WithLp 2 (Rn m × Rn k))).reindex (finCongr hfin)).repr
  let E : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn (m + k) := e.toContinuousLinearEquiv
  -- Step 3: `e⁻¹` is a volume-preserving measurable embedding, so
  -- `∫_{e(f(B))} g ∘ e⁻¹ = ∫_{f(B)} g`.
  have hes : MeasurePreserving e.symm volume volume := e.symm.measurePreserving
  have h1 : ∫⁻ v in e '' (f '' B), g (e.symm v) = ∫⁻ w in f '' B, g w := by
    rw [hes.setLIntegral_comp_emb e.symm.toHomeomorph.measurableEmbedding]
    congr 2
    rw [Set.image_image]
    simp
  -- Step 4: `e ∘ f` has derivative `E ∘ f'(u)` within `B` and is injective on `B`.
  have hder : ∀ u ∈ B, HasFDerivWithinAt (fun u ↦ e (f u)) (E.comp (f' u)) B u := fun u hu ↦
    E.hasFDerivAt.comp_hasFDerivWithinAt u (hf u hu)
  have hinj' : InjOn (fun u ↦ e (f u)) B := fun a ha b hb hab ↦ hinj ha hb (e.injective hab)
  -- Step 5: Mathlib's change of variables for `e ∘ f` and the integrand `g ∘ e⁻¹`.
  have h2 := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hB hder hinj'
    (fun v ↦ g (e.symm v))
  -- Step 7: combine; on `B` it remains to compare the Jacobians, as `e⁻¹ (e (f u)) = f u`.
  rw [← h1, Set.image_image, h2]
  refine setLIntegral_congr_fun hB (fun u hu ↦ ?_)
  simp only [LinearIsometryEquiv.symm_apply_apply]
  congr 2
  -- Step 6: `|det (E ∘ f'(u))| = normDet E · normDet (f'(u)) = normDet (f'(u))`.
  have hE : (E : WithLp 2 (Rn m × Rn k) →ₗ[ℝ] Rn (m + k)).normDet = 1 :=
    LinearIsometry.normDet_eq_one e.toLinearIsometry
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, ← LinearMap.normDet_eq_abs_det,
    LinearMap.normDet_comp_of_finrank_eq _ _ (by rw [hfin, finrank_euclideanSpace_fin]), hE,
    one_mul]
/-- **Pointwise Jacobian identity on a `C¹` chart** (steps 1 and 7 of the supplied proof of the
chart formula for the `C¹` parametric co-area formula, Simon Ch. 3, (2.8)–(2.9)). Let `Φ` be an
open partial homeomorphism from `ℝ^{m+k}` to `ℝᵐ × ℝᵏ` (Euclidean product) such that `Φ` and `Φ⁻¹`
are `C¹`, whose first component is `G`, and let `ψ` be `C¹` on `Φ.source`. If the flat Jacobian
identity (FJ) holds for `(m, k, N)`, then at every `u ∈ Φ.source`, with `j z = (0, z)`,
`normDet(D(ψ ∘ Φ⁻¹)(Φ u) ∘ j) · normDet(DΦ(u)) = normDet(Dψ(u) ∘ ι_{ker DG(u)}) · normDet(DG(u)*)`:
`DΦ(u)` and `DΦ⁻¹(Φ u)` are mutually inverse, `DG(u) = fst ∘ DΦ(u)`, and (FJ) applies to
`A = Dψ(u)`, `Γ = DG(u)`, `T = DΦ(u)` and `E = DΦ⁻¹(Φ u) ∘ j`. -/
theorem Submission.pcoarea_chart_pointwise_jacobian : ∀ (m k N : ℕ) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m) (Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k))), ContDiffOn ℝ 1 ψ Φ.source → ContDiffOn ℝ 1 Φ Φ.source → ContDiffOn ℝ 1 Φ.symm Φ.target → (∀ u ∈ Φ.source, (Φ u).fst = G u) → (∀ (A : Rn (m + k) →ₗ[ℝ] Rn N) (Γ : Rn (m + k) →ₗ[ℝ] Rn m) (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) (E : Rn k →ₗ[ℝ] Rn (m + k)), Function.Bijective T → (∀ v, (T v).fst = Γ v) → (∀ z, T (E z) = WithLp.toLp 2 (0, z)) → (A ∘ₗ E).normDet * T.normDet = (A ∘ₗ (LinearMap.ker Γ).subtype).normDet * (LinearMap.adjoint Γ).normDet) → ∀ u ∈ Φ.source, ((fderiv ℝ (ψ ∘ Φ.symm) (Φ u)).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet * (fderiv ℝ Φ u).toLinearMap.normDet = ((fderiv ℝ ψ u).toLinearMap ∘ₗ (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet * (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet := by
  intro m k N ψ G Φ hψ hΦ hΦs hfst hFJ u hu
  set j : Rn k →L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (Rn m) (Rn k))
  have hw : Φ u ∈ Φ.target := Φ.map_source hu
  have hleft : Φ.symm (Φ u) = u := Φ.left_inv hu
  -- Step 1: `Φ`, `Φ⁻¹` and `ψ` are differentiable at `u`, `Φ u` and `u` (`C¹` on open sets).
  have hΦd : DifferentiableAt ℝ Φ u :=
    (hΦ.differentiableOn one_ne_zero u hu).differentiableAt (Φ.open_source.mem_nhds hu)
  have hΦsd : DifferentiableAt ℝ Φ.symm (Φ u) :=
    (hΦs.differentiableOn one_ne_zero _ hw).differentiableAt (Φ.open_target.mem_nhds hw)
  have hψd : DifferentiableAt ℝ ψ u :=
    (hψ.differentiableOn one_ne_zero u hu).differentiableAt (Φ.open_source.mem_nhds hu)
  set T := fderiv ℝ Φ u
  set Λ := fderiv ℝ Φ.symm (Φ u)
  -- Step 2: `Λ ∘ T = id`, as `Φ⁻¹ ∘ Φ = id` near `u`.
  have hLT : Λ.comp T = ContinuousLinearMap.id ℝ _ := by
    have h1 : HasFDerivAt (Φ.symm ∘ Φ) (Λ.comp T) u := hΦsd.hasFDerivAt.comp u hΦd.hasFDerivAt
    have h2 : HasFDerivAt (Φ.symm ∘ Φ) (ContinuousLinearMap.id ℝ _) u := by
      apply (hasFDerivAt_id u).congr_of_eventuallyEq
      filter_upwards [Φ.open_source.mem_nhds hu] with x hx
      exact Φ.left_inv hx
    exact h1.unique h2
  -- Step 3: `T ∘ Λ = id`, as `Φ ∘ Φ⁻¹ = id` near `Φ u`.
  have hTL : T.comp Λ = ContinuousLinearMap.id ℝ _ := by
    have hΦd' : HasFDerivAt Φ T (Φ.symm (Φ u)) := by rw [hleft]; exact hΦd.hasFDerivAt
    have h1 : HasFDerivAt (Φ ∘ Φ.symm) (T.comp Λ) (Φ u) := hΦd'.comp (Φ u) hΦsd.hasFDerivAt
    have h2 : HasFDerivAt (Φ ∘ Φ.symm) (ContinuousLinearMap.id ℝ _) (Φ u) := by
      apply (hasFDerivAt_id (Φ u)).congr_of_eventuallyEq
      filter_upwards [Φ.open_target.mem_nhds hw] with x hx
      exact Φ.right_inv hx
    exact h1.unique h2
  -- Step 4: `T` is bijective.
  have hbij : Function.Bijective (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) := by
    constructor
    · intro v v' h
      have h' : Λ (T v) = Λ (T v') := congrArg Λ h
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, hLT] at h'
      simpa using h'
    · intro p
      refine ⟨Λ p, ?_⟩
      show T (Λ p) = p
      rw [← ContinuousLinearMap.comp_apply, hTL]
      rfl
  -- Step 5: `G = fst ∘ Φ` near `u`, so `DG(u) = fst ∘ T`.
  have hG : fderiv ℝ G u = (WithLp.fstL 2 ℝ (Rn m) (Rn k)).comp T := by
    have heq : G =ᶠ[𝓝 u] (fun x ↦ (Φ x).fst) := by
      filter_upwards [Φ.open_source.mem_nhds hu] with x hx
      exact (hfst x hx).symm
    rw [heq.fderiv_eq]
    exact ((WithLp.fstL 2 ℝ (Rn m) (Rn k)).hasFDerivAt.comp u hΦd.hasFDerivAt).fderiv
  have hfstT : ∀ v, ((T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) v).fst =
      (fderiv ℝ G u : Rn (m + k) →ₗ[ℝ] Rn m) v := by
    intro v
    rw [hG]
    rfl
  -- Step 6: `E = Λ ∘ j` satisfies `T (E z) = (0, z)`.
  let E : Rn k →ₗ[ℝ] Rn (m + k) := ((Λ.comp j : Rn k →L[ℝ] Rn (m + k)) : Rn k →ₗ[ℝ] Rn (m + k))
  have hE : ∀ z, (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) (E z) = WithLp.toLp 2 (0, z) := by
    intro z
    show T (Λ (j z)) = _
    rw [← ContinuousLinearMap.comp_apply, hTL]
    rfl
  -- Step 7: chain rule, `D(ψ ∘ Φ⁻¹)(Φ u) = Dψ(u) ∘ Λ`.
  have hchain : fderiv ℝ (ψ ∘ Φ.symm) (Φ u) = (fderiv ℝ ψ u).comp Λ := by
    have hψd' : DifferentiableAt ℝ ψ (Φ.symm (Φ u)) := by rw [hleft]; exact hψd
    rw [fderiv_comp (Φ u) hψd' hΦsd, hleft]
  -- Step 8: (FJ) with `A = Dψ(u)`, `Γ = DG(u)`, `T` and `E`.
  rw [hchain]
  exact hFJ (fderiv ℝ ψ u) (fderiv ℝ G u) T E hbij hfstT hE
/-- **Area formula for a `C¹` map that is injective on an open parameter domain** (Simon Ch. 2,
(3.2) and its weighted form (3.5), cf. (4.13)). Let `V ⊆ ℝᵏ` be open and `χ : ℝᵏ → ℝᴺ` be `C¹`
and injective on `V`; no rank condition on `Dχ` is assumed. Then for every Borel `S ⊆ V` and
Borel `φ ≥ 0`, `∫_{χ(S)} φ dHᵏ = ∫_S φ(χ(z)) J(z) dLᵏ(z)` with `J(z) = normDet (Dχ(z))`.

The Lipschitz area formula of the pinned `simongmt` package (`Chapter02.AreaDomain`) is not in the
import closure of the contract, so the formula is derived here for `C¹` maps from Mathlib's
change of variables in equal dimension and the linear area formula:
* if `Dχ(z)` is injective, let `P` be the orthogonal projection onto its range, read in an
  orthonormal basis. On a small ball `P` is `1`-Lipschitz on `χ(A)` and has a `K`-Lipschitz
  inverse there, and the same holds for `Dχ(w)` in place of `χ`; with the change of variables
  for `P ∘ χ` this gives `∫_A J ≤ Kᵏ Hᵏ(χ(A))` and `Hᵏ(χ(A)) ≤ Kᵏ ∫_A J`;
* if `Dχ(z)` is not injective, compressing a unit kernel direction by `δ` shows
  `Hᵏ(χ(A)) ≤ (‖Dχ(z)‖ + 2)ᵏ δ Lᵏ(A)` on a small ball;
* Lindelöf, Lusin–Souslin (Borel images, `MeasurableSet.image_of_continuousOn_injOn`) and
  `K → 1`, `δ → 0` give `Hᵏ(χ(A)) = ∫_A J` for Borel `A ⊆ V`; the weighted formula follows by
  pushing `J Lᵏ ⌞ S` forward under `χ`. -/
theorem Submission.pcoarea_c1_injOn_area_formula : ∀ (k N : ℕ) (V : Set (Rn k))
    (χ : Rn k → Rn N), IsOpen V → ContDiffOn ℝ 1 χ V → InjOn χ V → ∀ S ⊆ V, MeasurableSet S →
    ∀ φ : Rn N → ℝ≥0∞, Measurable φ → ∫⁻ x in χ '' S, φ x ∂μHE[k] =
      ∫⁻ z in S, φ (χ z) * ENNReal.ofReal ((fderiv ℝ χ z).toLinearMap.normDet) := by
  intro k N V χ hV hχ hinj S hSV hS φ hφ
  /- Step 1: measure-theoretic tools. `Hᵏ = Lᵏ` on `ℝᵏ`; the linear area formula; images under
  a map with a `K`-Lipschitz inverse; continuity of `normDet`. -/
  have hvolE : (μHE[k] : Measure (Rn k)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume k
  have hlinarea : ∀ (L : Rn k →L[ℝ] Rn N) (s : Set (Rn k)),
      μHE[k] (L '' s) = ENNReal.ofReal L.toLinearMap.normDet * volume s := by
    intro L s
    have h := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
      (L : Rn k →ₗ[ℝ] Rn N) s
    rwa [finrank_euclideanSpace_fin] at h
  have hlipInv : ∀ (s : Set (Rn k)) (g : Rn k → Rn k) (f : Rn k → Rn N) (K : ℝ≥0),
      (∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ K * ‖g x - g y‖) →
        μHE[k] (f '' s) ≤ (K : ℝ≥0∞) ^ k * volume (g '' s) := by
    intro s g f K hKf
    have hfeq : ∀ x ∈ s, f (Function.invFunOn g s (g x)) = f x := by
      intro x hx
      have hmem := Function.invFunOn_mem (f := g) (b := g x) ⟨x, hx, rfl⟩
      have heq := Function.invFunOn_eq (f := g) (b := g x) ⟨x, hx, rfl⟩
      have h := hKf _ hmem x hx
      rw [heq, sub_self, norm_zero, mul_zero] at h
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    have himage : f '' s = (f ∘ Function.invFunOn g s) '' (g '' s) := by
      rw [← Set.image_comp]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, hfeq x hx⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, (hfeq x hx).symm⟩
    have hLip : LipschitzOnWith K (f ∘ Function.invFunOn g s) (g '' s) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [Function.comp_apply, dist_eq_norm, hfeq x hx, hfeq y hy]
      exact hKf x hx y hy
    rw [himage, ← hvolE]
    exact Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k hLip
  have hndcont : Continuous (fun L : Rn k →L[ℝ] Rn N ↦ L.toLinearMap.normDet) := by
    have h1 : Continuous (fun L : Rn k →L[ℝ] Rn N ↦ ContinuousLinearMap.adjoint L ∘L L) :=
      ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id
    have h2 : Continuous (fun L : Rn k →L[ℝ] Rn N ↦
        Real.sqrt (ContinuousLinearMap.adjoint L ∘L L).det) :=
      Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp h1)
    refine h2.congr fun L ↦ ?_
    rw [← ContinuousLinearMap.normDet_sq L]
    exact Real.sqrt_sq (LinearMap.normDet_nonneg _)
  -- Step 2: `χ` is strictly differentiable on `V`, `Dχ` is continuous there, and images of Borel
  -- subsets of `V` are Borel and disjoint for disjoint sets (Lusin–Souslin, injectivity).
  have hdiff : ∀ z ∈ V, HasFDerivAt χ (fderiv ℝ χ z) z := fun z hz =>
    (((hχ.differentiableOn one_ne_zero) z hz).differentiableAt (hV.mem_nhds hz)).hasFDerivAt
  have hstrict : ∀ z ∈ V, HasStrictFDerivAt χ (fderiv ℝ χ z) z := fun z hz =>
    (hχ.contDiffAt (hV.mem_nhds hz)).hasStrictFDerivAt one_ne_zero
  have hfcont : ContinuousOn (fderiv ℝ χ) V := hχ.continuousOn_fderiv_of_isOpen hV le_rfl
  have hχcont : ContinuousOn χ V := hχ.continuousOn
  have hJcont : ContinuousOn (fun z ↦ (fderiv ℝ χ z).toLinearMap.normDet) V :=
    hndcont.comp_continuousOn hfcont
  have himg : ∀ A ⊆ V, MeasurableSet A → MeasurableSet (χ '' A) := fun A hAV hA =>
    hA.image_of_continuousOn_injOn (hχcont.mono hAV) (hinj.mono hAV)
  have hdisjimg : ∀ A B : Set (Rn k), A ⊆ V → B ⊆ V → Disjoint A B →
      Disjoint (χ '' A) (χ '' B) := by
    intro A B hAV hBV hAB
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba : b = a := hinj (hBV hb) (hAV ha) hab
    exact Set.disjoint_left.mp hAB ha (hba ▸ hb)
  /- Step 3 (regular points): if `Dχ(z)` is injective and `K > 1`, then on a small ball
  `∫_A J ≤ Kᵏ Hᵏ(χ(A))` and `Hᵏ(χ(A)) ≤ Kᵏ ∫_A J`. -/
  have hreg : ∀ z ∈ V, (fderiv ℝ χ z).toLinearMap.normDet ≠ 0 → ∀ K : ℝ≥0, 1 < K →
      ∃ r > 0, Metric.ball z r ⊆ V ∧ ∀ A ⊆ Metric.ball z r, MeasurableSet A →
        μHE[k] (χ '' A) ≤ (K : ℝ≥0∞) ^ k *
            ∫⁻ w in A, ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet ∧
          ∫⁻ w in A, ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet ≤
            (K : ℝ≥0∞) ^ k * μHE[k] (χ '' A) := by
    intro z hz hJz K hK
    set T : Rn k →L[ℝ] Rn N := fderiv ℝ χ z with hTdef
    -- `T` is injective, with a lower bound `‖v‖ ≤ c₀ ‖T v‖`
    have hker : LinearMap.ker T.toLinearMap = ⊥ := by
      by_contra h
      exact hJz (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr h)
    have hTinj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
    obtain ⟨c₀, hc₀, hanti⟩ := T.toLinearMap.exists_antilipschitzWith hker
    have hlow : ∀ v, ‖v‖ ≤ c₀ * ‖T v‖ := by
      intro v
      simpa [dist_eq_norm] using hanti.le_mul_dist v 0
    -- `P`: the orthogonal projection onto `range T`, read in an orthonormal basis of the range
    set R := LinearMap.range T.toLinearMap with hRdef
    have hRrank : finrank ℝ R = k := by
      rw [LinearMap.finrank_range_of_inj hTinj, finrank_euclideanSpace_fin]
    let b : OrthonormalBasis (Fin k) ℝ R := (stdOrthonormalBasis ℝ R).reindex (finCongr hRrank)
    let P : Rn N →L[ℝ] Rn k :=
      (b.repr.toContinuousLinearEquiv : R →L[ℝ] Rn k) ∘L R.orthogonalProjectionOnto
    have hP1 : ∀ y, ‖P y‖ ≤ ‖y‖ := by
      intro y
      have h1 : ‖P y‖ = ‖R.orthogonalProjectionOnto y‖ := by
        simp only [P, ContinuousLinearMap.comp_apply]
        exact b.repr.norm_map _
      rw [h1]
      exact (R.orthogonalProjectionOnto.le_opNorm y).trans
        (mul_le_of_le_one_left (norm_nonneg y) R.orthogonalProjectionOnto_norm_le)
    have hPT : ∀ v, ‖P (T v)‖ = ‖T v‖ := by
      intro v
      have hmem : T v ∈ R := LinearMap.mem_range_self T.toLinearMap v
      have h1 : R.orthogonalProjectionOnto (T v) = ⟨T v, hmem⟩ :=
        R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T v, hmem⟩
      simp only [P, ContinuousLinearMap.comp_apply, h1]
      exact b.repr.norm_map _
    -- the approximation constant `δ`, with `θ = c₀ δ ≤ min (1/4) ((K - 1)/4)`
    have hK1 : (1 : ℝ) < K := by exact_mod_cast hK
    have hc₀pos : (0 : ℝ) < c₀ := by exact_mod_cast hc₀
    obtain ⟨θ, hθpos, hθ14, hθK⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧ θ ≤ ((K : ℝ) - 1) / 4 :=
      ⟨min (1 / 4) (((K : ℝ) - 1) / 4), lt_min (by norm_num) (by linarith), min_le_left _ _,
        min_le_right _ _⟩
    obtain ⟨δ, hδpos, hc₀δ⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ (c₀ : ℝ) * δ = θ :=
      ⟨⟨θ / c₀, (div_pos hθpos hc₀pos).le⟩, div_pos hθpos hc₀pos, mul_div_cancel₀ θ hc₀pos.ne'⟩
    have hδ0 : (0 : ℝ) ≤ δ := δ.2
    -- core estimate for any map `f` approximating `T` with constant `δ` on `s`:
    -- `P ∘ f` is injective on `s`, `P` is `1`-Lipschitz, and `f = h ∘ P ∘ f` with `h` `K`-Lipschitz
    have core : ∀ (f : Rn k → Rn N) (s : Set (Rn k)), ApproximatesLinearOn f T s δ →
        InjOn (P ∘ f) s ∧ volume ((P ∘ f) '' s) ≤ μHE[k] (f '' s) ∧
          μHE[k] (f '' s) ≤ (K : ℝ≥0∞) ^ k * volume ((P ∘ f) '' s) := by
      intro f s hf
      have key : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ K * ‖P (f x) - P (f y)‖ ∧
          3 * ‖x - y‖ ≤ 4 * c₀ * ‖P (f x) - P (f y)‖ := by
        intro x hx y hy
        have he : ‖f x - f y - T (x - y)‖ ≤ δ * ‖x - y‖ := hf x hx y hy
        have hPe : ‖P (f x - f y - T (x - y))‖ ≤ δ * ‖x - y‖ := (hP1 _).trans he
        have ht : ‖T (x - y)‖ ≤ ‖P (f x) - P (f y)‖ + δ * ‖x - y‖ := by
          have h : P (T (x - y)) = (P (f x) - P (f y)) - P (f x - f y - T (x - y)) := by
            rw [map_sub P (f x - f y), map_sub P (f x)]; abel
          rw [← hPT, h]
          exact (norm_sub_le _ _).trans (by linarith)
        have hq : ‖f x - f y‖ ≤ ‖T (x - y)‖ + δ * ‖x - y‖ := by
          have h : f x - f y = T (x - y) + (f x - f y - T (x - y)) := by abel
          calc ‖f x - f y‖ = ‖T (x - y) + (f x - f y - T (x - y))‖ := congrArg _ h
            _ ≤ ‖T (x - y)‖ + ‖f x - f y - T (x - y)‖ := norm_add_le _ _
            _ ≤ ‖T (x - y)‖ + δ * ‖x - y‖ := by linarith
        have ha : ‖x - y‖ ≤ c₀ * ‖T (x - y)‖ := hlow (x - y)
        have hp0 : 0 ≤ ‖P (f x) - P (f y)‖ := norm_nonneg _
        have ha0 : 0 ≤ ‖x - y‖ := norm_nonneg _
        have h1 := mul_le_mul_of_nonneg_left ht hc₀pos.le
        have h1' : (c₀ : ℝ) * (δ * ‖x - y‖) = θ * ‖x - y‖ := by rw [← mul_assoc, hc₀δ]
        have hθa := mul_le_mul_of_nonneg_right hθ14 ha0
        have h2 : 3 * ‖x - y‖ ≤ 4 * c₀ * ‖P (f x) - P (f y)‖ := by
          rw [mul_add, h1'] at h1
          linarith
        refine ⟨?_, h2⟩
        have h3 := mul_le_mul_of_nonneg_left h2 hδ0
        have h3' : (δ : ℝ) * (4 * c₀ * ‖P (f x) - P (f y)‖) = 4 * θ * ‖P (f x) - P (f y)‖ := by
          rw [← hc₀δ]; ring
        have hθp := mul_le_mul_of_nonneg_right hθK hp0
        have hKp : 0 ≤ ((K : ℝ) - 1) * ‖P (f x) - P (f y)‖ := mul_nonneg (by linarith) hp0
        rw [h3'] at h3
        linarith
      refine ⟨?_, ?_, ?_⟩
      · intro x hx y hy hxy
        have h := (key x hx y hy).2
        have hxy' : P (f x) - P (f y) = 0 := sub_eq_zero.mpr hxy
        rw [hxy', norm_zero, mul_zero] at h
        have h0 : ‖x - y‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
        exact sub_eq_zero.mp (norm_eq_zero.mp h0)
      · rw [Set.image_comp, ← hvolE]
        have hLipP : LipschitzOnWith 1 P (f '' s) := by
          apply LipschitzOnWith.of_dist_le_mul
          intro y₁ _ y₂ _
          rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
          exact hP1 _
        simpa using
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k hLipP
      · exact hlipInv s (P ∘ f) f K (fun x hx y hy => (key x hx y hy).1)
    -- choose the radius: `χ` approximates `T` and `‖Dχ - T‖ < δ` on the ball, which lies in `V`
    obtain ⟨s₀, hs₀, happrox⟩ :=
      (hstrict z hz).approximates_deriv_on_nhds (c := δ) (Or.inr hδpos)
    have hcontz : ContinuousAt (fderiv ℝ χ) z := hfcont.continuousAt (hV.mem_nhds hz)
    have hev : ∀ᶠ w in 𝓝 z, ‖fderiv ℝ χ w - T‖ < δ := by
      have := hcontz.eventually (Metric.ball_mem_nhds T (show (0 : ℝ) < δ from hδpos))
      filter_upwards [this] with w hw
      rwa [dist_eq_norm] at hw
    obtain ⟨r, hr, hball⟩ :=
      Metric.mem_nhds_iff.mp (inter_mem (inter_mem hs₀ (hV.mem_nhds hz)) hev)
    refine ⟨r, hr, fun w hw => (hball hw).1.2, ?_⟩
    intro A hAr hA
    have hAV : A ⊆ V := fun w hw => (hball (hAr hw)).1.2
    obtain ⟨hinjA, hlowA, hupA⟩ :=
      core χ A (happrox.mono_set fun w hw => (hball (hAr hw)).1.1)
    -- change of variables for `P ∘ χ` (Mathlib, equal dimension)
    have hcov : ∫⁻ w in A, ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| =
        volume ((P ∘ χ) '' A) :=
      lintegral_abs_det_fderiv_eq_addHaar_image volume hA
        (fun w hw => (P.hasFDerivAt.comp w (hdiff w (hAV hw))).hasFDerivWithinAt) hinjA
    -- pointwise comparison of `|det (P ∘ Dχ(w))|` with `J(w)`, from `core` for `Dχ(w)`
    have hlin : ∀ w ∈ Metric.ball z r,
        ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| ≤
            ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet ∧
          ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet ≤
            (K : ℝ≥0∞) ^ k * ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| := by
      intro w hw
      set L := fderiv ℝ χ w
      have hLT : ‖L - T‖ < δ := (hball hw).2
      have happL : ApproximatesLinearOn (L : Rn k → Rn N) T univ δ := by
        intro x _ y _
        have h : L x - L y - T (x - y) = (L - T) (x - y) := by
          simp only [sub_apply, map_sub]; abel
        rw [h]
        exact ((L - T).le_opNorm _).trans (mul_le_mul_of_nonneg_right hLT.le (norm_nonneg _))
      obtain ⟨-, hlow', hup'⟩ := core L (Metric.ball 0 1) (happL.mono_set (subset_univ _))
      have h1 : volume ((P ∘ L) '' Metric.ball 0 1) =
          ENNReal.ofReal |(P ∘L L).det| * volume (Metric.ball (0 : Rn k) 1) :=
        Measure.addHaar_image_continuousLinearMap volume (P ∘L L) _
      rw [h1, hlinarea L (Metric.ball 0 1)] at hlow' hup'
      have hB0 : volume (Metric.ball (0 : Rn k) 1) ≠ 0 :=
        (Metric.measure_ball_pos volume (0 : Rn k) one_pos).ne'
      have hBtop : volume (Metric.ball (0 : Rn k) 1) ≠ ⊤ := measure_ball_lt_top.ne
      constructor
      · exact (ENNReal.mul_le_mul_iff_left hB0 hBtop).mp hlow'
      · rw [← mul_assoc] at hup'
        exact (ENNReal.mul_le_mul_iff_left hB0 hBtop).mp hup'
    constructor
    · calc μHE[k] (χ '' A) ≤ (K : ℝ≥0∞) ^ k * volume ((P ∘ χ) '' A) := hupA
        _ = (K : ℝ≥0∞) ^ k * ∫⁻ w in A, ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| := by
            rw [hcov]
        _ ≤ (K : ℝ≥0∞) ^ k *
              ∫⁻ w in A, ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet :=
            mul_le_mul_right (setLIntegral_mono' hA fun w hw => (hlin w (hAr hw)).1) _
    · calc ∫⁻ w in A, ENNReal.ofReal (fderiv ℝ χ w).toLinearMap.normDet
          ≤ ∫⁻ w in A, (K : ℝ≥0∞) ^ k * ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| :=
            setLIntegral_mono' hA fun w hw => (hlin w (hAr hw)).2
        _ = (K : ℝ≥0∞) ^ k * ∫⁻ w in A, ENNReal.ofReal |(P ∘L fderiv ℝ χ w).det| :=
            lintegral_const_mul' _ _ (by simp)
        _ = (K : ℝ≥0∞) ^ k * volume ((P ∘ χ) '' A) := by rw [hcov]
        _ ≤ (K : ℝ≥0∞) ^ k * μHE[k] (χ '' A) := mul_le_mul_right hlowA _
  /- Step 4 (critical points): if `Dχ(z)` is not injective and `ε > 0`, then on a small ball
  `Hᵏ(χ(A)) ≤ ε Lᵏ(A)`. -/
  have hcrit : ∀ z ∈ V, (fderiv ℝ χ z).toLinearMap.normDet = 0 → ∀ ε : ℝ≥0, 0 < ε →
      ∃ r > 0, Metric.ball z r ⊆ V ∧ ∀ A ⊆ Metric.ball z r,
        μHE[k] (χ '' A) ≤ ε * volume A := by
    intro z hz hJz ε hε
    set T : Rn k →L[ℝ] Rn N := fderiv ℝ χ z with hTdef
    -- a unit vector `u` in the kernel of `T`
    have hker : LinearMap.ker T.toLinearMap ≠ ⊥ :=
      LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp hJz
    obtain ⟨u₀, hu₀mem, hu₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    set u : Rn k := (‖u₀‖⁻¹ : ℝ) • u₀ with hudef
    have hu1 : ‖u‖ = 1 := norm_smul_inv_norm hu₀ne
    have hTu : T u = 0 := by
      have h0 : T u₀ = 0 := hu₀mem
      rw [hudef, map_smul, h0, smul_zero]
    have huu : inner ℝ u u = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hu1]; norm_num
    -- constants: `M = ‖T‖ + 2` and `δ ≤ 1` with `Mᵏ δ ≤ ε`
    set M : ℝ≥0 := ‖T‖₊ + 2 with hM
    have hMpos : 0 < M := by positivity
    set δ : ℝ≥0 := min 1 (ε / M ^ k) with hδ
    have hδpos : 0 < δ := lt_min one_pos (div_pos hε (pow_pos hMpos k))
    have hδ1 : (δ : ℝ) ≤ 1 := by exact_mod_cast min_le_left _ _
    have hMδ : M ^ k * δ ≤ ε := by
      calc M ^ k * δ ≤ M ^ k * (ε / M ^ k) := mul_le_mul_right (min_le_right _ _) _
        _ = ε := mul_div_cancel₀ _ (pow_pos hMpos k).ne'
    -- the compression `S x = x + (δ - 1) ⟪u, x⟫ u`
    let S : Rn k →L[ℝ] Rn k :=
      ContinuousLinearMap.id ℝ (Rn k) + ((δ : ℝ) - 1) • (innerSL ℝ u).smulRight u
    have hS : ∀ x, S x = x + (((δ : ℝ) - 1) * inner ℝ u x) • u := by
      intro x
      simp only [S, add_apply, ContinuousLinearMap.id_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
    have hSnorm : ∀ x, ‖x - (inner ℝ u x) • u‖ ≤ ‖S x‖ ∧ (δ : ℝ) * |inner ℝ u x| ≤ ‖S x‖ := by
      intro x
      set a := inner ℝ u x with ha
      have horth : inner ℝ (x - a • u) (((δ : ℝ) * a) • u) = 0 := by
        rw [inner_smul_right, inner_sub_left, inner_smul_left, huu, real_inner_comm, ← ha]
        simp
      have hSx : S x = (x - a • u) + ((δ : ℝ) * a) • u := by
        rw [hS, ← ha, sub_mul, one_mul, sub_smul]
        abel
      have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      rw [← hSx] at hpy
      have hnu : ‖((δ : ℝ) * a) • u‖ = (δ : ℝ) * |a| := by
        rw [norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_mul, NNReal.abs_eq]
      rw [hnu] at hpy
      have h0 : 0 ≤ (δ : ℝ) * |a| := mul_nonneg δ.2 (abs_nonneg a)
      constructor
      · refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr ?_
        rw [hpy]
        exact le_add_of_nonneg_right (mul_self_nonneg _)
      · refine (mul_self_le_mul_self_iff h0 (norm_nonneg _)).mpr ?_
        rw [hpy]
        exact le_add_of_nonneg_left (mul_self_nonneg _)
    -- `det S = δ`, computed in an orthonormal basis containing `u`
    have hdetS : LinearMap.det (S : Rn k →ₗ[ℝ] Rn k) = δ := by
      have hk : k ≠ 0 := by
        rintro rfl
        exact hu₀ne (Subsingleton.elim _ _)
      set i₀ : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
      obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
        (E := Rn k) (ι := Fin k) (by simp) (v := fun _ => u) (s := {i₀}) (by
          rw [orthonormal_iff_ite]
          rintro ⟨i, hi⟩ ⟨j, hj⟩
          simp only [Set.mem_singleton_iff] at hi hj
          subst hi hj
          simp [hu1])
      have hbi₀ : b i₀ = u := hb i₀ rfl
      rw [← LinearMap.det_toMatrix b.toBasis]
      have hmat : LinearMap.toMatrix b.toBasis b.toBasis (S : Rn k →ₗ[ℝ] Rn k) =
          Matrix.diagonal (fun i => if i = i₀ then (δ : ℝ) else 1) := by
        ext i j
        rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis,
          ContinuousLinearMap.coe_coe, hS, inner_add_right, inner_smul_right, ← hbi₀,
          b.inner_eq_ite, b.inner_eq_ite, b.inner_eq_ite, Matrix.diagonal_apply]
        by_cases hij : i = j
        · subst hij
          by_cases hi : i = i₀
          · subst hi; simp
          · simp [hi, Ne.symm hi]
        · by_cases hj : i₀ = j
          · subst hj; simp [hij]
          · simp [hij, hj]
      rw [hmat, Matrix.det_diagonal, Finset.prod_ite_eq' Finset.univ i₀ (fun _ => (δ : ℝ))]
      simp
    -- choose the radius: `χ` approximates `T` with constant `δ` on the ball
    obtain ⟨s₀, hs₀, happrox⟩ :=
      (hstrict z hz).approximates_deriv_on_nhds (c := δ) (Or.inr hδpos)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hs₀ (hV.mem_nhds hz))
    refine ⟨r, hr, fun w hw => (hball hw).2, ?_⟩
    intro A hAr
    have happA : ApproximatesLinearOn χ T A δ := happrox.mono_set fun w hw => (hball (hAr hw)).1
    -- `‖χ x - χ y‖ ≤ M ‖S x - S y‖` on `A`, since `T` kills the compressed direction
    have hkey : ∀ x ∈ A, ∀ y ∈ A, ‖χ x - χ y‖ ≤ M * ‖S x - S y‖ := by
      intro x hx y hy
      set Δ := x - y with hΔ
      set a := inner ℝ u Δ with ha
      have he : ‖χ x - χ y - T Δ‖ ≤ δ * ‖Δ‖ := happA x hx y hy
      have hTΔ : T Δ = T (Δ - a • u) := by
        rw [T.map_sub Δ (a • u), T.map_smul, hTu, smul_zero, sub_zero]
      have hTb : ‖T (Δ - a • u)‖ ≤ ‖T‖ * ‖Δ - a • u‖ := T.le_opNorm _
      have hΔle : ‖Δ‖ ≤ ‖Δ - a • u‖ + |a| := by
        calc ‖Δ‖ = ‖(Δ - a • u) + a • u‖ := by rw [sub_add_cancel]
          _ ≤ ‖Δ - a • u‖ + ‖a • u‖ := norm_add_le _ _
          _ = ‖Δ - a • u‖ + |a| := by rw [norm_smul, hu1, mul_one, Real.norm_eq_abs]
      obtain ⟨h1, h2⟩ := hSnorm Δ
      rw [← ha, hΔ, map_sub] at h1 h2
      have hq : ‖χ x - χ y‖ ≤ ‖T Δ‖ + δ * ‖Δ‖ := by
        calc ‖χ x - χ y‖ = ‖T Δ + (χ x - χ y - T Δ)‖ := by rw [add_sub_cancel]
          _ ≤ ‖T Δ‖ + ‖χ x - χ y - T Δ‖ := norm_add_le _ _
          _ ≤ ‖T Δ‖ + δ * ‖Δ‖ := by linarith
      have hM' : (M : ℝ) = ‖T‖ + 2 := by simp [M]
      rw [hTΔ] at hq
      rw [hM']
      have hδ0 : (0 : ℝ) ≤ δ := δ.2
      have h3 := mul_le_mul_of_nonneg_left hΔle hδ0
      have h4 := mul_le_mul_of_nonneg_right hδ1 (norm_nonneg (Δ - a • u))
      have h5 := mul_le_mul_of_nonneg_left h1 (norm_nonneg T)
      linarith
    calc μHE[k] (χ '' A) ≤ (M : ℝ≥0∞) ^ k * volume (S '' A) := hlipInv A S χ M hkey
      _ = (M : ℝ≥0∞) ^ k * ((δ : ℝ≥0∞) * volume A) := by
          rw [Measure.addHaar_image_continuousLinearMap, hdetS, NNReal.abs_eq,
            ENNReal.ofReal_coe_nnreal]
      _ = ((M ^ k * δ : ℝ≥0) : ℝ≥0∞) * volume A := by push_cast; ring
      _ ≤ ε * volume A := mul_le_mul_left (by exact_mod_cast hMδ) _
  /- Step 5: localization (Lindelöf). A property of Borel sets that is stable under countable
  disjoint unions and holds for Borel subsets of small balls around each point of `W` holds for
  all Borel subsets of `W`. -/
  have hloc : ∀ (W : Set (Rn k)) (Pr : Set (Rn k) → Prop), Pr ∅ →
      (∀ A : ℕ → Set (Rn k), (∀ i, MeasurableSet (A i)) →
        Pairwise (Function.onFun Disjoint A) → (∀ i, Pr (A i)) → Pr (⋃ i, A i)) →
      (∀ z ∈ W, ∃ r > 0, ∀ A, MeasurableSet A → A ⊆ Metric.ball z r → Pr A) →
      ∀ A, MeasurableSet A → A ⊆ W → Pr A := by
    intro W Pr h0 hU hlocal A hA hAW
    choose! r hr hPr using hlocal
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun z : W => Metric.ball (z : Rn k) (r z)) (fun _ => Metric.isOpen_ball)
    have hcov : A ⊆ ⋃ i ∈ T, Metric.ball (i : Rn k) (r i) := by
      rw [hT]
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hAW hx⟩, Metric.mem_ball_self (hr x (hAW hx))⟩
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · have hAe : A = ∅ := by
        rw [hTe] at hcov
        simpa using hcov
      rw [hAe]
      exact h0
    obtain ⟨e, he⟩ := hTc.exists_eq_range hTne
    set B : ℕ → Set (Rn k) := fun n => A ∩ Metric.ball (e n : Rn k) (r (e n)) with hB
    have hBmeas : ∀ n, MeasurableSet (B n) := fun n => hA.inter measurableSet_ball
    have hAeq : A = ⋃ n, disjointed B n := by
      rw [iUnion_disjointed]
      apply Subset.antisymm
      · intro x hx
        have hx' := hcov hx
        rw [he] at hx'
        simp only [mem_iUnion, mem_range, exists_prop] at hx'
        obtain ⟨i, ⟨n, rfl⟩, hxi⟩ := hx'
        exact mem_iUnion.mpr ⟨n, hx, hxi⟩
      · exact iUnion_subset fun n => inter_subset_left
    rw [hAeq]
    apply hU
    · exact MeasurableSet.disjointed hBmeas
    · exact disjoint_disjointed B
    · intro n
      exact hPr _ (e n).2 _ (MeasurableSet.disjointed hBmeas n)
        ((disjointed_subset B n).trans inter_subset_right)
  -- Step 6: two limit arguments in `[0, ∞]`
  have hlim : ∀ a b : ℝ≥0∞, (∀ K : ℝ≥0, 1 < K → a ≤ (K : ℝ≥0∞) ^ k * b) → a ≤ b := by
    intro a b h
    by_cases hb : b = ⊤
    · rw [hb]; exact le_top
    have h1 : Tendsto (fun K : ℝ≥0 => (K : ℝ≥0∞) ^ k) (𝓝 1) (𝓝 1) := by
      have hc : Continuous (fun K : ℝ≥0 => (K : ℝ≥0∞) ^ k) :=
        (ENNReal.continuous_pow k).comp ENNReal.continuous_coe
      simpa using hc.tendsto 1
    have ht : Tendsto (fun K : ℝ≥0 => (K : ℝ≥0∞) ^ k * b) (𝓝[>] 1) (𝓝 b) := by
      simpa using (ENNReal.Tendsto.mul_const h1 (Or.inr hb)).mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun K hK => h K hK)
  have hzero : ∀ a c : ℝ≥0∞, c ≠ ⊤ → (∀ ε : ℝ≥0, 0 < ε → a ≤ ε * c) → a = 0 := by
    intro a c hc h
    have h1 : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
      simpa using ENNReal.continuous_coe.tendsto 0
    have ht : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * c) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.Tendsto.mul_const h1 (Or.inr hc)).mono_left nhdsWithin_le_nhds
    exact le_antisymm (ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => h ε hε))
      zero_le
  -- Step 7: the regular set `G = {J ≠ 0}` (open) and the critical set `Z = V \ G`
  set G : Set (Rn k) := V ∩ (fun z ↦ (fderiv ℝ χ z).toLinearMap.normDet) ⁻¹' {0}ᶜ with hG
  have hGopen : IsOpen G := hJcont.isOpen_inter_preimage hV isOpen_compl_singleton
  set Z : Set (Rn k) := V \ G with hZ
  -- on Borel subsets of `G`: `Hᵏ(χ(A)) = ∫_A J`
  have hregG : ∀ A, MeasurableSet A → A ⊆ G →
      μHE[k] (χ '' A) = ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet := by
    intro A hA hAG
    have hbounds : ∀ K : ℝ≥0, 1 < K →
        μHE[k] (χ '' A) ≤ (K : ℝ≥0∞) ^ k *
            ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet ∧
          ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet ≤
            (K : ℝ≥0∞) ^ k * μHE[k] (χ '' A) := by
      intro K hK
      refine hloc G (fun A => A ⊆ V → (μHE[k] (χ '' A) ≤ (K : ℝ≥0∞) ^ k *
            ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet ∧
          ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet ≤
            (K : ℝ≥0∞) ^ k * μHE[k] (χ '' A))) ?_ ?_ ?_ A hA hAG (hAG.trans inter_subset_left)
      · intro _
        simp
      · intro As hAs hdisj hPr hUV
        have hAsV : ∀ i, As i ⊆ V := fun i => (subset_iUnion As i).trans hUV
        have h1 : μHE[k] (χ '' ⋃ i, As i) = ∑' i, μHE[k] (χ '' As i) := by
          rw [image_iUnion]
          exact measure_iUnion (fun i j hij => hdisjimg _ _ (hAsV i) (hAsV j) (hdisj hij))
            (fun i => himg _ (hAsV i) (hAs i))
        have h2 : ∫⁻ z in ⋃ i, As i, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet =
            ∑' i, ∫⁻ z in As i, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet :=
          lintegral_iUnion hAs hdisj _
        rw [h1, h2, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        exact ⟨ENNReal.tsum_le_tsum fun i => ((hPr i) (hAsV i)).1,
          ENNReal.tsum_le_tsum fun i => ((hPr i) (hAsV i)).2⟩
      · intro z hz
        obtain ⟨r, hr, -, hb⟩ := hreg z hz.1 hz.2 K hK
        exact ⟨r, hr, fun A hA hAr _ => hb A hAr hA⟩
    exact le_antisymm (hlim _ _ fun K hK => (hbounds K hK).1)
      (hlim _ _ fun K hK => (hbounds K hK).2)
  -- on Borel subsets of `Z`: `Hᵏ(χ(A)) = 0`
  have hcritZ : ∀ A, MeasurableSet A → A ⊆ Z → μHE[k] (χ '' A) = 0 := by
    intro A hA hAZ
    have hball : ∀ n : ℕ, μHE[k] (χ '' (A ∩ Metric.ball 0 n)) = 0 := by
      intro n
      apply hzero _ (volume (Metric.ball (0 : Rn k) n)) measure_ball_lt_top.ne
      intro ε hε
      have hle := hloc Z (fun A => μHE[k] (χ '' A) ≤ ε * volume A) (by simp) ?_ ?_
        (A ∩ Metric.ball 0 n) (hA.inter measurableSet_ball) (inter_subset_left.trans hAZ)
      · exact hle.trans (mul_le_mul_right (measure_mono inter_subset_right) _)
      · intro As hAs hdisj hPr
        calc μHE[k] (χ '' ⋃ i, As i) = μHE[k] (⋃ i, χ '' As i) := by rw [image_iUnion]
          _ ≤ ∑' i, μHE[k] (χ '' As i) := measure_iUnion_le _
          _ ≤ ∑' i, ε * volume (As i) := ENNReal.tsum_le_tsum hPr
          _ = ε * volume (⋃ i, As i) := by rw [ENNReal.tsum_mul_left, measure_iUnion hdisj hAs]
      · intro z hz
        have hJz : (fderiv ℝ χ z).toLinearMap.normDet = 0 := by
          by_contra h
          exact hz.2 ⟨hz.1, h⟩
        obtain ⟨r, hr, -, hb⟩ := hcrit z hz.1 hJz ε hε
        exact ⟨r, hr, fun A _ hAr => hb A hAr⟩
    have hAU : χ '' A = ⋃ n : ℕ, χ '' (A ∩ Metric.ball 0 n) := by
      rw [← image_iUnion, ← inter_iUnion, Metric.iUnion_ball_nat, inter_univ]
    rw [hAU]
    exact measure_iUnion_null hball
  -- Step 8: the area formula `Hᵏ(χ(A)) = ∫_A J` for Borel `A ⊆ V`
  have hmain : ∀ A ⊆ V, MeasurableSet A →
      μHE[k] (χ '' A) = ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet := by
    intro A hAV hA
    have hAG : MeasurableSet (A ∩ G) := hA.inter hGopen.measurableSet
    have hAZ : MeasurableSet (A ∩ Z) := hA.inter (hV.measurableSet.diff hGopen.measurableSet)
    have hAsplit : A = (A ∩ G) ∪ (A ∩ Z) := by
      rw [← inter_union_distrib_left, hZ, union_sdiff_cancel inter_subset_left,
        inter_eq_left.mpr hAV]
    have hJZ : ∫⁻ z in A ∩ Z, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet = 0 := by
      rw [setLIntegral_congr_fun hAZ (g := fun _ => 0) (fun z hz => by
        have hJz : (fderiv ℝ χ z).toLinearMap.normDet = 0 := by
          by_contra h
          exact hz.2.2 ⟨hz.2.1, h⟩
        simp [hJz])]
      simp
    have hint : ∫⁻ z in A, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet =
        ∫⁻ z in A ∩ G, ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet := by
      conv_lhs => rw [hAsplit]
      rw [lintegral_union hAZ (Disjoint.mono inter_subset_right inter_subset_right
        disjoint_sdiff_right), hJZ, add_zero]
    have hcz := hcritZ (A ∩ Z) hAZ inter_subset_right
    rw [hint, ← hregG (A ∩ G) hAG inter_subset_right]
    apply le_antisymm
    · calc μHE[k] (χ '' A) = μHE[k] (χ '' (A ∩ G) ∪ χ '' (A ∩ Z)) := by
            rw [← image_union, ← hAsplit]
        _ ≤ μHE[k] (χ '' (A ∩ G)) + μHE[k] (χ '' (A ∩ Z)) := measure_union_le _ _
        _ = μHE[k] (χ '' (A ∩ G)) := by rw [hcz, add_zero]
    · exact measure_mono (image_mono inter_subset_left)
  -- Step 9: the weighted formula, pushing `J Lᵏ ⌞ S` forward under (a Borel version of) `χ`
  classical
  set u : Rn k → Rn N := S.piecewise χ 0 with hu
  have humeas : Measurable u := (hχcont.mono hSV).measurable_piecewise continuousOn_const hS
  have hueq : ∀ z ∈ S, u z = χ z := fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
  have hmap : Measure.map u ((volume.restrict S).withDensity
      (fun z ↦ ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet)) =
        (μHE[k] : Measure (Rn N)).restrict (χ '' S) := by
    ext B hB
    rw [Measure.map_apply humeas hB, withDensity_apply _ (humeas hB),
      Measure.restrict_restrict (humeas hB), Measure.restrict_apply hB,
      ← hmain _ (inter_subset_right.trans hSV) ((humeas hB).inter hS)]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨hzB, hzS⟩, rfl⟩
      exact ⟨by rwa [mem_preimage, hueq z hzS] at hzB, z, hzS, rfl⟩
    · rintro ⟨hyB, z, hzS, rfl⟩
      exact ⟨z, ⟨by rwa [mem_preimage, hueq z hzS], hzS⟩, rfl⟩
  have hJae : AEMeasurable (fun z ↦ ENNReal.ofReal (fderiv ℝ χ z).toLinearMap.normDet)
      (volume.restrict S) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hJcont.mono hSV).aemeasurable hS)
  rw [← hmap, lintegral_map hφ humeas, lintegral_withDensity_eq_lintegral_mul₀ hJae
    (g := fun z ↦ φ (u z)) (hφ.comp humeas).aemeasurable]
  refine setLIntegral_congr_fun hS fun z hz => ?_
  simp only [Pi.mul_apply, hueq z hz]
  exact mul_comm _ _
/-- **Block-triangular factorization of `normDet`** (steps 1 and 6 of the flat Jacobian identity
for the co-area formula, Simon Ch. 3, (2.7)–(2.8)). Let `Γ : ℝ^{m+k} → ℝᵐ` be surjective and
`S : ℝ^{m+k} → ℝᵏ` linear, let `T : ℝ^{m+k} → WithLp 2 (ℝᵐ × ℝᵏ)` have components `Γ` and `S`,
and let `K = ker Γ`. Then `normDet T = normDet (Γ|_{K^⊥}) · normDet (S|_K)`. In the coordinates
`c(a, b) = a + b`, a linear isometry `WithLp 2 (K^⊥ × K) ≃ ℝ^{m+k}`, and orthonormal bases of
`K^⊥`, `K`, `ℝᵐ`, `ℝᵏ`, the matrix of `T ∘ c` is block lower-triangular because `Γ` vanishes on
`K`; its diagonal blocks are the matrices of `Γ|_{K^⊥}` and `S|_K`. -/
theorem Submission.pcoarea_flat_normDet_block : ∀ (m k : ℕ) (Γ : Rn (m + k) →ₗ[ℝ] Rn m) (S : Rn (m + k) →ₗ[ℝ] Rn k) (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)), Function.Surjective Γ → (∀ v, (T v).fst = Γ v) → (∀ v, (T v).snd = S v) → T.normDet = (Γ.domRestrict (LinearMap.ker Γ)ᗮ).normDet * (S ∘ₗ (LinearMap.ker Γ).subtype).normDet := by
  intro m k Γ S T hΓ hfst hsnd
  -- Step 1: `dim K = k` by rank–nullity (`Γ` is onto), hence `dim K^⊥ = m`.
  have hK : finrank ℝ (LinearMap.ker Γ) = k := by
    have h := LinearMap.finrank_range_add_finrank_ker Γ
    rw [LinearMap.range_eq_top.mpr hΓ, finrank_top, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin] at h
    omega
  have hKp : finrank ℝ (LinearMap.ker Γ)ᗮ = m := by
    have h := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker Γ)
    rw [hK, finrank_euclideanSpace_fin] at h
    omega
  -- Step 2: `c(a, b) = a + b` is a linear isometry `WithLp 2 (K^⊥ × K) ≃ ℝ^{m+k}`, so
  -- `normDet (T ∘ c) = normDet T · normDet c = normDet T`.
  let c : WithLp 2 ((LinearMap.ker Γ)ᗮ × LinearMap.ker Γ) ≃ₗᵢ[ℝ] Rn (m + k) :=
    ((LinearMap.ker Γ).orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdComm 2 ℝ _ _)).symm
  have hc : ∀ p, c p = (p.fst : Rn (m + k)) + (p.snd : Rn (m + k)) := by
    intro p
    change ((p.snd : Rn (m + k)) + (p.fst : Rn (m + k))) = _
    exact add_comm _ _
  have hTc : (T ∘ₗ c.toLinearEquiv.toLinearMap).normDet = T.normDet := by
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ c.toLinearEquiv.finrank_eq,
      show c.toLinearEquiv.toLinearMap.normDet = 1 from c.toLinearIsometry.normDet_eq_one,
      mul_one]
  -- Steps 3–5: in the product orthonormal bases `β₁.prod β₂` of `WithLp 2 (K^⊥ × K)` and
  -- `γ₁.prod γ₂` of `WithLp 2 (ℝᵐ × ℝᵏ)`, the matrix of `T ∘ c` has the blocks
  -- `⟨γ₁ i, Γ (β₁ j)⟩`, `⟨γ₁ i, Γ (β₂ j)⟩ = 0` (as `β₂ j ∈ ker Γ`), `⟨γ₂ i, S (β₁ j)⟩` and
  -- `⟨γ₂ i, S (β₂ j)⟩`.
  let β₁ : OrthonormalBasis (Fin m) ℝ (LinearMap.ker Γ)ᗮ :=
    (stdOrthonormalBasis ℝ (LinearMap.ker Γ)ᗮ).reindex (finCongr hKp)
  let β₂ : OrthonormalBasis (Fin k) ℝ (LinearMap.ker Γ) :=
    (stdOrthonormalBasis ℝ (LinearMap.ker Γ)).reindex (finCongr hK)
  let γ₁ := EuclideanSpace.basisFun (Fin m) ℝ
  let γ₂ := EuclideanSpace.basisFun (Fin k) ℝ
  have hmat : LinearMap.toMatrix (β₁.prod β₂).toBasis (γ₁.prod γ₂).toBasis
      (T ∘ₗ c.toLinearEquiv.toLinearMap) =
      Matrix.fromBlocks
        (LinearMap.toMatrix β₁.toBasis γ₁.toBasis (Γ.domRestrict (LinearMap.ker Γ)ᗮ)) 0
        (LinearMap.toMatrix β₁.toBasis γ₂.toBasis (S.domRestrict (LinearMap.ker Γ)ᗮ))
        (LinearMap.toMatrix β₂.toBasis γ₂.toBasis (S ∘ₗ (LinearMap.ker Γ).subtype)) := by
    have hc' : ∀ x, c.toLinearEquiv x = c x := fun _ => rfl
    ext (i | i) (j | j) <;>
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.prod_apply,
        OrthonormalBasis.repr_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        LinearMap.comp_apply, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
        WithLp.prod_inner_apply, LinearMap.domRestrict_apply, Submodule.subtype_apply] <;>
      simp [hc', hc, hfst, hsnd]
  -- Steps 6–7: `det (fromBlocks M₁₁ 0 M₂₁ M₂₂) = det M₁₁ · det M₂₂`, and `normDet` is `‖det‖` of
  -- the matrix in orthonormal bases indexed by the same type.
  rw [← hTc, LinearMap.normDet_eq_norm_det_toMatrix _ (β₁.prod β₂) (γ₁.prod γ₂), hmat,
    Matrix.det_fromBlocks_zero₁₂, norm_mul,
    ← LinearMap.normDet_eq_norm_det_toMatrix _ β₁ γ₁,
    ← LinearMap.normDet_eq_norm_det_toMatrix _ β₂ γ₂]
/-- **Section identity for the flat co-area Jacobian** (steps (i) and (iv) of the flat-Jacobian
computation behind Simon Ch. 3, (2.7)–(2.8)). Let `K ⊆ ℝⁿ` be a subspace with `dim K = k`,
`ι_K : K → ℝⁿ` its inclusion, and `E : ℝᵏ → ℝⁿ` linear with range in `K` and left inverse
`S : ℝⁿ → ℝᵏ`. Then `normDet(A ∘ E) normDet(S ∘ ι_K) = normDet(A ∘ ι_K)` for every linear
`A : ℝⁿ → ℝᴺ`. Corestricting `E` to `E' : ℝᵏ → K` gives `A ∘ E = (A ∘ ι_K) ∘ E'` and
`(S ∘ ι_K) ∘ E' = id`; as `dim ℝᵏ = dim K`, `normDet` is multiplicative on both composites, so
`normDet(A ∘ E) = normDet(A ∘ ι_K) normDet(E')` and `normDet(S ∘ ι_K) normDet(E') = 1`. -/
theorem Submission.pcoarea_flat_normDet_section : ∀ (n k N : ℕ) (A : Rn n →ₗ[ℝ] Rn N) (K : Submodule ℝ (Rn n)) (S : Rn n →ₗ[ℝ] Rn k) (E : Rn k →ₗ[ℝ] Rn n), Module.finrank ℝ K = k → (∀ z, E z ∈ K) → (∀ z, S (E z) = z) → (A ∘ₗ E).normDet * (S ∘ₗ K.subtype).normDet = (A ∘ₗ K.subtype).normDet := by
  intro n k N A K S E hK hEK hSE
  -- Step 1: corestrict `E` to `E' : ℝᵏ → K`; then `A ∘ E = (A ∘ ι_K) ∘ E'`.
  let E' : Rn k →ₗ[ℝ] K := E.codRestrict K hEK
  have hAE : A ∘ₗ E = (A ∘ₗ K.subtype) ∘ₗ E' := rfl
  -- Step 2: `(S ∘ ι_K) ∘ E' = id`.
  have hSE' : (S ∘ₗ K.subtype) ∘ₗ E' = LinearMap.id := LinearMap.ext hSE
  -- Step 3: `dim ℝᵏ = k = dim K`.
  have hdim : finrank ℝ (Rn k) = finrank ℝ K := by rw [finrank_euclideanSpace_fin, hK]
  -- Steps 4–5: `normDet` is multiplicative on both composites.
  have h4 := LinearMap.normDet_comp_of_finrank_eq E' (A ∘ₗ K.subtype) hdim
  have h5 := LinearMap.normDet_comp_of_finrank_eq E' (S ∘ₗ K.subtype) hdim
  rw [hSE', LinearMap.normDet_id] at h5
  -- Step 6: `normDet(A ∘ E) normDet(S ∘ ι_K) = normDet(A ∘ ι_K) (normDet(S ∘ ι_K) normDet(E'))`.
  rw [hAE, h4, mul_right_comm, mul_assoc, ← h5, mul_one]

/-- **Flat Jacobian identity**: the linear algebra behind the co-area formula 2.7–2.8 of Simon
Ch. 3 (`chapter-03.txt` lines 411–425), which "follows from the `C¹` case". Let `n = m + k`,
`T : ℝⁿ → WithLp 2 (ℝᵐ × ℝᵏ)` be bijective with first component `Γ` and `T (E z) = (0, z)`, and
`K = ker Γ`. Then `normDet (A ∘ E) · normDet T = normDet (A ∘ ι_K) · normDet Γ*`.
`Γ` is onto (as `T` is), so `dim K = k`. With `S` the second component of `T`, `E` maps into `K`
and `S ∘ E = id`, whence `normDet (A ∘ E) · normDet (S ∘ ι_K) = normDet (A ∘ ι_K)`
(`pcoarea_flat_normDet_section`). In the orthogonal splitting `ℝⁿ = K^⊥ ⊕ K`, `T` is block lower
triangular, so `normDet T = normDet (Γ|_{K^⊥}) · normDet (S ∘ ι_K)`
(`pcoarea_flat_normDet_block`). Finally `Γ*`, corestricted to `K^⊥ = range Γ*`, is the adjoint
of the square map `Γ|_{K^⊥}` and so has the same `normDet`. No property of `A` is used. -/
theorem Submission.pcoarea_flat_jacobian_identity : ∀ (m k N : ℕ) (A : Rn (m + k) →ₗ[ℝ] Rn N)
    (Γ : Rn (m + k) →ₗ[ℝ] Rn m) (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k))
    (E : Rn k →ₗ[ℝ] Rn (m + k)), Function.Bijective T → (∀ v, (T v).fst = Γ v) →
    (∀ z, T (E z) = WithLp.toLp 2 (0, z)) →
    (A ∘ₗ E).normDet * T.normDet =
      (A ∘ₗ (LinearMap.ker Γ).subtype).normDet * (LinearMap.adjoint Γ).normDet := by
  intro m k N A Γ T E hT hfst hE
  -- Step 1: `Γ = fst ∘ T` is surjective because `T` is, so `K = ker Γ` has dimension `k`.
  have hΓ : Function.Surjective Γ := by
    intro y
    obtain ⟨v, hv⟩ := hT.2 (WithLp.toLp 2 (y, 0))
    exact ⟨v, by rw [← hfst, hv, WithLp.toLp_fst]⟩
  have hK : finrank ℝ (LinearMap.ker Γ) = k := by
    have h := LinearMap.finrank_range_add_finrank_ker Γ
    rw [LinearMap.range_eq_top.mpr hΓ, finrank_top, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin] at h
    omega
  -- Step 2: `T v = (Γ v, S v)` with `S = snd ∘ T`; `E` maps into `K` and `S ∘ E = id`.
  obtain ⟨S, hsnd⟩ : ∃ S : Rn (m + k) →ₗ[ℝ] Rn k, ∀ v, (T v).snd = S v :=
    ⟨WithLp.sndₗ 2 ℝ (Rn m) (Rn k) ∘ₗ T, fun v ↦ rfl⟩
  have hEK : ∀ z, E z ∈ LinearMap.ker Γ := by
    intro z
    rw [LinearMap.mem_ker, ← hfst, hE, WithLp.toLp_fst]
  have hSE : ∀ z, S (E z) = z := by
    intro z
    rw [← hsnd, hE, WithLp.toLp_snd]
  -- Steps 3–4: `normDet (A ∘ E) · normDet (S ∘ ι_K) = normDet (A ∘ ι_K)`.
  have hsec := Submission.pcoarea_flat_normDet_section (m + k) k N A (LinearMap.ker Γ) S E hK
    hEK hSE
  -- Step 6: `normDet T = normDet (Γ|_{K^⊥}) · normDet (S ∘ ι_K)`.
  have hblock := Submission.pcoarea_flat_normDet_block m k Γ S T hΓ hfst hsnd
  -- Step 5: `normDet (Γ|_{K^⊥}) = normDet Γ*`.
  have hadj : (Γ.domRestrict (LinearMap.ker Γ)ᗮ).normDet = (LinearMap.adjoint Γ).normDet := by
    have hm : ∀ y, LinearMap.adjoint Γ y ∈ (LinearMap.ker Γ)ᗮ := by
      intro y
      rw [LinearMap.orthogonal_ker]
      exact ⟨y, rfl⟩
    have ha : (LinearMap.adjoint Γ).codRestrict (LinearMap.ker Γ)ᗮ hm =
        LinearMap.adjoint (Γ.domRestrict (LinearMap.ker Γ)ᗮ) := by
      apply (LinearMap.eq_adjoint_iff _ _).mpr
      intro y x
      exact LinearMap.adjoint_inner_left Γ x y
    have hd : finrank ℝ (LinearMap.ker Γ)ᗮ = finrank ℝ (Rn m) := by
      have h := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker Γ)
      rw [hK, finrank_euclideanSpace_fin] at h
      rw [finrank_euclideanSpace_fin]
      omega
    classical
    let b₁ := stdOrthonormalBasis ℝ (LinearMap.ker Γ)ᗮ
    let b₂ := (stdOrthonormalBasis ℝ (Rn m)).reindex (finCongr hd.symm)
    rw [← LinearMap.normDet_codRestrict hm, ha,
      (LinearMap.adjoint _).normDet_eq_norm_det_toMatrix b₂ b₁,
      (Γ.domRestrict _).normDet_eq_norm_det_toMatrix b₁ b₂, LinearMap.toMatrix_adjoint,
      Matrix.det_conjTranspose]
    simp
  -- Step 7: combine.
  rw [hblock, ← hsec, hadj]
  ring
/-- **Critical part of the parametric co-area formula** (parent steps 0(a) and 1). On
`B ⊆ Crit = {u | DG(u) not surjective}` the Jacobian vanishes: `ker DG(u)* = (range DG(u))ᗮ ≠ 0`,
so `normDet DG(u)* = 0` and the left side is `0`. On the right, `ψ` is `C¹` on the open set `D`,
hence locally Lipschitz there; by Lindelöf and Ch. 2, Thm. 1.8(i) (SimonGMT
`euclideanHausdorffMeasure_image_le_of_lipschitzOn`) it maps `Hᵏ`-null subsets of `D` to `Hᵏ`-null
sets. For `Lᵐ`-a.e. `y`, `Hᵏ(B ∩ G⁻¹{y}) ≤ Hᵏ(Crit ∩ G⁻¹{y}) = 0`, so the inner integral over
`ψ(B ∩ G⁻¹{y})` vanishes: the inner function is a.e. `0`, hence a.e.-measurable with integral `0`.
Neither measurability of `φ` nor any regularity of `G` is needed. -/
theorem Submission.pcoarea_critical_part : ∀ (m k N : ℕ) (D : Set (Rn (m + k)))
    (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m), IsOpen D → ContDiffOn ℝ 1 ψ D →
    (∀ᵐ y ∂(volume : Measure (Rn m)),
      μHE[k] ({u | ¬ Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}) = 0) →
    ∀ B ⊆ D, MeasurableSet B → B ⊆ {u | ¬ Function.Surjective (fderiv ℝ G u)} →
    ∀ φ : Rn N → ℝ≥0∞, Measurable φ →
    AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧
    ∫⁻ u in B, φ (ψ u) * ENNReal.ofReal (((fderiv ℝ ψ u).toLinearMap ∘ₗ
      (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet *
      (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet) =
    ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
  intro m k N D ψ G hD hψ hcrit B hBD hB hBcrit φ hφ
  -- Step 1: on `B`, `DG(u)` is not surjective, so `normDet (DG(u)*) = 0` and the left side is `0`.
  have hdet : ∀ u ∈ B, (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet = 0 := by
    intro u hu
    rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot, ← LinearMap.orthogonal_range, Ne,
      Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]
    exact hBcrit hu
  have hlhs : ∫⁻ u in B, φ (ψ u) * ENNReal.ofReal (((fderiv ℝ ψ u).toLinearMap ∘ₗ
      (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet *
      (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet) = 0 := by
    refine (setLIntegral_congr_fun hB fun u hu ↦ ?_).trans lintegral_zero
    simp only [hdet u hu, mul_zero, ENNReal.ofReal_zero]
  -- Step 2: `ψ` is locally Lipschitz on the open set `D`, so it maps `Hᵏ`-null subsets of `D`
  -- to `Hᵏ`-null sets (Lindelöf and countable subadditivity).
  have hnull : ∀ S ⊆ D, μHE[k] S = 0 → μHE[k] (ψ '' S) = 0 := by
    intro S hSD hS
    have hloc : ∀ x ∈ S, ∃ o : Set (Rn (m + k)), IsOpen o ∧ x ∈ o ∧
        ∃ K : ℝ≥0, LipschitzOnWith K ψ o := by
      intro x hx
      obtain ⟨K, t, ht, hK⟩ := (hψ.contDiffAt (hD.mem_nhds (hSD hx))).exists_lipschitzOnWith
      obtain ⟨o, hot, ho, hxo⟩ := mem_nhds_iff.mp ht
      exact ⟨o, ho, hxo, K, hK.mono hot⟩
    choose! o ho hxo K hK using hloc
    obtain ⟨T, hTS, hTc, hTo⟩ := TopologicalSpace.isOpen_biUnion_countable S o ho
    have hcover : ψ '' S ⊆ ⋃ x ∈ T, ψ '' (S ∩ o x) := by
      rintro _ ⟨z, hz, rfl⟩
      have hzT : z ∈ ⋃ x ∈ T, o x := by
        rw [hTo]
        exact mem_biUnion hz (hxo z hz)
      obtain ⟨x, hxT, hzx⟩ := mem_iUnion₂.mp hzT
      exact mem_iUnion₂.mpr ⟨x, hxT, z, ⟨hz, hzx⟩, rfl⟩
    have hpiece : ∀ x ∈ T, μHE[k] (ψ '' (S ∩ o x)) = 0 := by
      intro x hx
      have hL : LipschitzOnWith (K x) ψ (S ∩ o x) := (hK x (hTS hx)).mono inter_subset_right
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k hL
      rw [measure_mono_null inter_subset_left hS, mul_zero] at h
      exact nonpos_iff_eq_zero.mp h
    exact measure_mono_null hcover ((measure_biUnion_null_iff hTc).2 hpiece)
  -- Step 3: for a.e. `y`, `Hᵏ(B ∩ G⁻¹{y}) = 0`, so `Hᵏ(ψ(B ∩ G⁻¹{y})) = 0` and the inner
  -- integral vanishes.
  have hae : (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) =ᵐ[volume]
      fun _ ↦ 0 := by
    filter_upwards [hcrit] with y hy
    exact setLIntegral_measure_zero _ _ (hnull _ (inter_subset_left.trans hBD)
      (measure_mono_null (inter_subset_inter_left _ hBcrit) hy))
  -- Step 4: the inner function is a.e. `0`, so it is a.e.-measurable and both sides are `0`.
  exact ⟨aemeasurable_const.congr hae.symm, by rw [hlhs, lintegral_congr_ae hae, lintegral_zero]⟩
/-- **Implicit-function chart at a regular point** (step 2, L2, of the parametric co-area
formula): if `G : ℝ^{m+k} → ℝᵐ` is `C¹` and `DG(u₀)` is onto, then `Φ = (G, π)`, restricted to a
neighbourhood of `u₀` inside the open set `D`, is a `C¹` chart onto an open subset of
`WithLp 2 (ℝᵐ × ℝᵏ)` with `C¹` inverse and first component `G`. Here `π = ι ∘ p`, where `p` is
the orthogonal projection onto `K₀ = ker DG(u₀)` (of dimension `k` by rank–nullity) and
`ι : K₀ ≃ₗᵢ ℝᵏ`; then `DΦ(u₀) = (DG(u₀), π)` is invertible. The inverse function theorem gives
`Φ` near `u₀`, and restricting it to `D ∩ {u : DΦ(u) invertible}` (open) makes `Φ⁻¹` `C¹` at
every point of the target. -/
theorem Submission.pcoarea_implicit_chart : ∀ (m k : ℕ) (G : Rn (m + k) → Rn m) (D : Set (Rn (m + k))) (u₀ : Rn (m + k)), IsOpen D → u₀ ∈ D → ContDiff ℝ 1 G → Function.Surjective (fderiv ℝ G u₀) → ∃ Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k)), u₀ ∈ Φ.source ∧ Φ.source ⊆ D ∧ ContDiffOn ℝ 1 Φ Φ.source ∧ ContDiffOn ℝ 1 Φ.symm Φ.target ∧ ∀ u ∈ Φ.source, (Φ u).fst = G u := by
  intro m k G D u₀ hD hu₀ hG hsurj
  -- Step 1: `K₀ = ker DG(u₀)` has dimension `k` (rank–nullity).
  set K₀ : Submodule ℝ (Rn (m + k)) := (fderiv ℝ G u₀).ker
  have hdim : finrank ℝ K₀ = k := by
    have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ G u₀).toLinearMap
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin] at h
    change m + finrank ℝ K₀ = m + k at h
    omega
  -- Step 2: `π = ι ∘ p` with `p` the orthogonal projection onto `K₀` and `ι : K₀ ≃ₗᵢ ℝᵏ`.
  let ι : K₀ ≃ₗᵢ[ℝ] Rn k := ((stdOrthonormalBasis ℝ K₀).reindex (finCongr hdim)).repr
  let π : Rn (m + k) →L[ℝ] Rn k :=
    (ι.toContinuousLinearEquiv : K₀ →L[ℝ] Rn k).comp K₀.orthogonalProjectionOnto
  have hπ : ∀ v : K₀, π v = ι v := fun v ↦ by
    simp [π, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  -- Step 3: `F = σ ∘ (G, π)` is `C¹`, with `DF(u) = σ ∘ (DG(u), π)`.
  let σ := (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm
  let F : Rn (m + k) → WithLp 2 (Rn m × Rn k) := fun u ↦ σ (G u, π u)
  have hF : ContDiff ℝ 1 F := σ.contDiff.comp (hG.prodMk π.contDiff)
  let L : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (σ : Rn m × Rn k →L[ℝ] WithLp 2 (Rn m × Rn k)).comp ((fderiv ℝ G u₀).prod π)
  have hFL : HasFDerivAt F L u₀ :=
    σ.hasFDerivAt.comp u₀ (((hG.differentiable one_ne_zero) u₀).hasFDerivAt.prodMk π.hasFDerivAt)
  -- Step 4: `DF(u₀)` is bijective.
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h0 : (fderiv ℝ G u₀ v, π v) = 0 := by
      simpa [L] using hv
    have hvK : v ∈ K₀ := LinearMap.mem_ker.mpr (congrArg Prod.fst h0)
    have hιv : ι ⟨v, hvK⟩ = 0 := by
      rw [← hπ]
      exact congrArg Prod.snd h0
    exact congrArg Subtype.val (ι.map_eq_zero_iff.mp hιv)
  have hsurjL : Function.Surjective L := by
    intro z
    obtain ⟨v₁, hv₁⟩ := hsurj z.fst
    let c : K₀ := ι.symm (z.snd - π v₁)
    refine ⟨v₁ + c, ?_⟩
    have h1 : fderiv ℝ G u₀ (c : Rn (m + k)) = 0 := LinearMap.mem_ker.mp c.2
    have h2 : π c = z.snd - π v₁ := by
      rw [hπ]
      exact ι.apply_symm_apply _
    have e1 : fderiv ℝ G u₀ (v₁ + c) = z.fst := by rw [map_add, h1, add_zero, hv₁]
    have e2 : π (v₁ + c) = z.snd := by rw [map_add, h2, add_sub_cancel]
    change σ (fderiv ℝ G u₀ (v₁ + c), π (v₁ + c)) = z
    rw [e1, e2]
    rfl
  let f' : Rn (m + k) ≃L[ℝ] WithLp 2 (Rn m × Rn k) :=
    ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurjL)
  have hf' : (f' : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) = L :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  -- Step 5: the inverse function theorem.
  have hstrict : HasStrictFDerivAt F (f' : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) u₀ :=
    hF.contDiffAt.hasStrictFDerivAt' (hf' ▸ hFL) one_ne_zero
  -- Step 6: restrict to `U = D ∩ W`, `W = {u : DF(u) is invertible}` (open).
  let W : Set (Rn (m + k)) := fderiv ℝ F ⁻¹' Set.range ContinuousLinearEquiv.toContinuousLinearMap
  have hW : IsOpen W := ContinuousLinearEquiv.isOpen.preimage (hF.continuous_fderiv one_ne_zero)
  have hu₀W : u₀ ∈ W := ⟨f', by rw [hFL.fderiv, ← hf']⟩
  have hU : IsOpen (D ∩ W) := hD.inter hW
  let Φ := (hstrict.toOpenPartialHomeomorph F).restrOpen (D ∩ W) hU
  have hΦ : (Φ : Rn (m + k) → WithLp 2 (Rn m × Rn k)) = F := by
    simp only [Φ, OpenPartialHomeomorph.coe_restrOpen,
      HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  -- Step 7: verification.
  refine ⟨Φ, ⟨hstrict.mem_toOpenPartialHomeomorph_source, hu₀, hu₀W⟩, fun u hu ↦ hu.2.1, ?_, ?_,
    ?_⟩
  · rw [hΦ]
    exact hF.contDiffOn
  · intro w hw
    have hsrc : Φ.symm w ∈ Φ.source := Φ.map_target hw
    obtain ⟨e, he⟩ := hsrc.2.2
    refine (Φ.contDiffAt_symm (f₀' := e) hw ?_ ?_).contDiffWithinAt
    · rw [hΦ]
      change HasFDerivAt F (e.toContinuousLinearMap) (Φ.symm w)
      rw [he]
      exact ((hF.differentiable one_ne_zero) _).hasFDerivAt
    · rw [hΦ]
      exact hF.contDiffAt
  · intro u hu
    rw [hΦ]
    rfl

/-- **Parametric co-area formula on one chart** (Simon Ch. 3, co-area formula 2.8–2.9, regular
part of the `C¹` case; cf. Federer 3.2.12, 3.2.22). Let `Φ` be an open partial homeomorphism from
`ℝⁿ`, `n = m + k`, to `P = WithLp 2 (ℝᵐ × ℝᵏ)`, `C¹` on its source `O` with `C¹` inverse on its
target, whose first component is `G` on `O`, and let `ψ` be `C¹` and injective on `O`. For Borel
`B ⊆ O` and Borel `φ ≥ 0`, `y ↦ ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ` is a.e. measurable and
`∫_B φ(ψ(u)) J(u) du = ∫_{ℝᵐ} ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ dy`, where
`J(u) = normDet (Dψ(u) ∘ ι_{ker DG(u)}) · normDet (DG(u)*)`.
With `ρ = ψ ∘ Φ⁻¹`, `j z = (0, z)`, `h = φ ∘ ρ · normDet (Dρ ∘ j)` and `F = 1_{Φ(B)} h` on `P`:
* each slice integral is `∫_{ℝᵏ} F(y, z) dz`, by the injective area formula on the slice
  `z ↦ ρ(y, z)` (`pcoarea_chart_slice_lintegral` with `pcoarea_c1_injOn_area_formula`);
* `y ↦ ∫ F(y, z) dz` is measurable and `∫_P F = ∫_{ℝᵐ} ∫_{ℝᵏ} F(y, z) dz dy` (Tonelli,
  `pcoarea_chart_integrand_tonelli`);
* `Φ(B)` is Borel (Lusin–Souslin), so `∫_P F = ∫_{Φ(B)} h = ∫_B normDet (DΦ(u)) h(Φ(u)) du`
  (`pcoarea_chart_change_of_variables`);
* `normDet (Dρ(Φ(u)) ∘ j) · normDet (DΦ(u)) = J(u)` (`pcoarea_chart_pointwise_jacobian` with the
  flat Jacobian identity `pcoarea_flat_jacobian_identity`). -/
theorem Submission.pcoarea_formula_on_chart : ∀ (m k N : ℕ) (ψ : Rn (m + k) → Rn N)
    (G : Rn (m + k) → Rn m) (Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k))),
    ContDiffOn ℝ 1 ψ Φ.source → InjOn ψ Φ.source → ContDiffOn ℝ 1 Φ Φ.source →
    ContDiffOn ℝ 1 Φ.symm Φ.target → (∀ u ∈ Φ.source, (Φ u).fst = G u) →
    ∀ B ⊆ Φ.source, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ →
    AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧
      ∫⁻ u in B, φ (ψ u) * ENNReal.ofReal (((fderiv ℝ ψ u).toLinearMap ∘ₗ
          (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet *
          (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet) =
        ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
  intro m k N ψ G Φ hψ hinj hΦ hΦs hfst B hB hBm φ hφ
  -- Steps 1–3: the area formula on every slice gives `∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ = ∫ F(y, z) dz`.
  have hslice := Submission.pcoarea_chart_slice_lintegral m k N ψ G Φ hψ hinj hΦs hfst B hB hBm φ
    (fun V χ hV hχ hχi S hSV hS ↦
      Submission.pcoarea_c1_injOn_area_formula k N V χ hV hχ hχi S hSV hS φ hφ)
  -- Steps 4–5: `F` is Borel, and Tonelli on `ℝᵐ × ℝᵏ` transported to `P`.
  obtain ⟨hmeas, htonelli⟩ :=
    Submission.pcoarea_chart_integrand_tonelli m k N ψ Φ hψ.continuousOn B hB hBm φ hφ
  -- First claim: the slice integral is everywhere equal to a measurable function of `y`.
  refine ⟨hmeas.aemeasurable.congr (Eventually.of_forall fun y ↦ (hslice y).symm), ?_⟩
  -- Step 6: `Φ(B)` is Borel and `Φ` has derivative `DΦ(u)` within `B` at each `u ∈ B`.
  have hΦB : MeasurableSet (Φ '' B) :=
    hBm.image_of_continuousOn_injOn (Φ.continuousOn.mono hB) (Φ.injOn.mono hB)
  have hder : ∀ u ∈ B, HasFDerivWithinAt Φ (fderiv ℝ Φ u) B u := fun u hu ↦
    ((hΦ.differentiableOn one_ne_zero u (hB hu)).differentiableAt
      (Φ.open_source.mem_nhds (hB hu))).hasFDerivAt.hasFDerivWithinAt
  -- Step 7: `normDet (Dρ(Φ(u)) ∘ j) · normDet (DΦ(u)) = J(u)` on the source.
  have hjac := Submission.pcoarea_chart_pointwise_jacobian m k N ψ G Φ hψ hΦ hΦs hfst
    (Submission.pcoarea_flat_jacobian_identity m k N)
  -- Second claim: `∫∫ = ∫_P F = ∫_{Φ(B)} h = ∫_B normDet (DΦ(u)) h(Φ(u)) du = ∫_B φ(ψ(u)) J(u) du`.
  rw [lintegral_congr hslice, ← htonelli, lintegral_indicator hΦB,
    Submission.pcoarea_chart_change_of_variables m k Φ (fderiv ℝ Φ) B hBm hder (Φ.injOn.mono hB)]
  refine setLIntegral_congr_fun hBm (fun u hu ↦ ?_)
  rw [← hjac u (hB hu), ENNReal.ofReal_mul (LinearMap.normDet_nonneg _), Φ.left_inv (hB hu)]
  ring
/-- **Lindelöf gluing of the parametric co-area identity**: the localization step of the proof of
the `C¹` co-area formula (Simon Ch. 2, 6.3 and 6.6, whose proof Simon omits; [Fed69, 3.2.12,
3.2.22]). Let `D ⊆ ℝⁿ` be open, `Z ⊆ ℝⁿ` arbitrary, `ψ : ℝⁿ → ℝᴺ` continuous and injective on `D`,
`G : ℝⁿ → ℝᵐ` continuous and `w ≥ 0` arbitrary. Call a Borel set `B ⊆ D` good if for every Borel
`φ ≥ 0` the function `y ↦ ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ` is `Lᵐ`-a.e. measurable and
`∫_B φ(ψ(u)) w(u) dLⁿ(u) = ∫_{ℝᵐ} ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ dLᵐ(y)`. If every Borel `B ⊆ D` with
`B ⊆ Z` is good, and every `p ∈ D \ Z` has an open neighbourhood `O` such that every Borel
`B ⊆ D ∩ O` is good, then every Borel `B ⊆ D` is good. By Lindelöf, countably many of these
neighbourhoods cover `D \ Z`. They cut `B` into disjoint Borel pieces, one inside `Z` and each of
the others inside a single neighbourhood. For every `y` the images `ψ(B_t ∩ G⁻¹{y})` of the
pieces' slices are Borel (Lusin–Souslin) and pairwise disjoint (`ψ` is injective on `D`), so both
sides of the identity are countably additive over the pieces. -/
theorem Submission.pcoarea_gluing : ∀ (n N m k : ℕ) (D Z : Set (Rn n)) (ψ : Rn n → Rn N) (G : Rn n → Rn m) (w : Rn n → ℝ≥0∞), IsOpen D → ContinuousOn ψ D → InjOn ψ D → Continuous G → (∀ B ⊆ D, MeasurableSet B → B ⊆ Z → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧ ∫⁻ u in B, φ (ψ u) * w u = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume) → (∀ p ∈ D, p ∉ Z → ∃ O : Set (Rn n), IsOpen O ∧ p ∈ O ∧ ∀ B ⊆ D ∩ O, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧ ∫⁻ u in B, φ (ψ u) * w u = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume) → ∀ B ⊆ D, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧ ∫⁻ u in B, φ (ψ u) * w u = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
  intro n N m k D Z ψ G w _hD hψc hψi hG hCrit hLoc B hBD hBm φ hφ
  classical
  -- Step 1 (Lindelöf): a good open neighbourhood `O p` of each `p ∈ D \ Z`, and a countable
  -- subfamily `(O i)_{i ∈ T}` with the same union.
  have hLoc' : ∀ p : ↥(D \ Z), ∃ O : Set (Rn n), IsOpen O ∧ (p : Rn n) ∈ O ∧
      ∀ B ⊆ D ∩ O, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ →
        AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧
          ∫⁻ u in B, φ (ψ u) * w u =
            ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume :=
    fun p ↦ hLoc p p.2.1 p.2.2
  choose O hOo hpO hOgood using hLoc'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hOo
  have hcovT : D \ Z ⊆ ⋃ i ∈ T, O i := by
    intro x hx
    rw [hTU]
    exact mem_iUnion.2 ⟨⟨x, hx⟩, hpO _⟩
  -- If the subfamily is empty (the case the proof pads with `∅`), then `D ⊆ Z`, so `B` is good
  -- by (Crit).
  by_cases hT : T.Nonempty
  swap
  · have hBZ : B ⊆ Z := by
      intro x hxB
      by_contra hxZ
      obtain ⟨i, hiT, -⟩ := mem_iUnion₂.1 (hcovT ⟨hBD hxB, hxZ⟩)
      exact hT ⟨i, hiT⟩
    exact hCrit B hBD hBm hBZ φ hφ
  -- Otherwise list it as a sequence `U j = O (e j)`, `j ∈ ℕ`, covering `D \ Z`.
  obtain ⟨e, he⟩ := hTc.exists_eq_range hT
  set U : ℕ → Set (Rn n) := fun j ↦ O (e j) with hUdef
  have hUo : ∀ j, IsOpen (U j) := fun j ↦ hOo _
  have hcover : D \ Z ⊆ ⋃ j, U j := by
    intro x hx
    obtain ⟨i, hiT, hxi⟩ := mem_iUnion₂.1 (hcovT hx)
    rw [he] at hiT
    obtain ⟨j, rfl⟩ := hiT
    exact mem_iUnion.2 ⟨j, hxi⟩
  -- Step 2 (disjoint pieces): `P = disjointed C` with `C 0 = B \ ⋃ j, U j` and
  -- `C (j + 1) = B ∩ U j`, so `P 0 = B \ ⋃ j, U j` and `P (j + 1) = (B ∩ U j) \ ⋃_{i < j} U i`.
  let C : ℕ → Set (Rn n) := fun t ↦ Nat.casesOn t (B \ ⋃ j, U j) (fun j ↦ B ∩ U j)
  have hCm : ∀ t, MeasurableSet (C t) := by
    intro t
    cases t with
    | zero => exact hBm.diff (MeasurableSet.iUnion fun j ↦ (hUo j).measurableSet)
    | succ j => exact hBm.inter (hUo j).measurableSet
  have hCB : ∀ t, C t ⊆ B := by
    intro t
    cases t with
    | zero => exact sdiff_subset
    | succ j => exact inter_subset_left
  have hCU : ⋃ t, C t = B := by
    refine Subset.antisymm (iUnion_subset hCB) fun x hxB ↦ ?_
    by_cases hx : x ∈ ⋃ j, U j
    · obtain ⟨j, hxj⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨j + 1, ⟨hxB, hxj⟩⟩
    · exact mem_iUnion.2 ⟨0, ⟨hxB, hx⟩⟩
  set P : ℕ → Set (Rn n) := disjointed C with hPdef
  have hPm : ∀ t, MeasurableSet (P t) := MeasurableSet.disjointed hCm
  have hPd : Pairwise (Function.onFun Disjoint P) := disjoint_disjointed C
  have hPU : ⋃ t, P t = B := by rw [hPdef, iUnion_disjointed, hCU]
  have hPC : ∀ t, P t ⊆ C t := disjointed_subset C
  have hPD : ∀ t, P t ⊆ D := fun t ↦ (hPC t).trans ((hCB t).trans hBD)
  -- Every piece is good: `P 0 ⊆ Z` by (Crit), and `P (j + 1) ⊆ D ∩ U j` by (Loc).
  have hPgood : ∀ t, ∀ φ : Rn N → ℝ≥0∞, Measurable φ →
      AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (P t ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧
        ∫⁻ u in P t, φ (ψ u) * w u =
          ∫⁻ y, (∫⁻ x in ψ '' (P t ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
    intro t
    cases t with
    | zero =>
      refine hCrit (P 0) (hPD 0) (hPm 0) fun x hx ↦ ?_
      have hx' : x ∈ B \ ⋃ j, U j := hPC 0 hx
      by_contra hxZ
      exact hx'.2 (hcover ⟨hBD hx'.1, hxZ⟩)
    | succ j =>
      refine hOgood (e j) (P (j + 1)) (fun x hx ↦ ⟨hPD _ hx, ?_⟩) (hPm _)
      have hx' : x ∈ B ∩ U j := hPC (j + 1) hx
      exact hx'.2
  -- Step 3 (slices): for each `y` the sets `ψ '' (P t ∩ G ⁻¹' {y})` are Borel (Lusin–Souslin)
  -- and pairwise disjoint, with union `ψ '' (B ∩ G ⁻¹' {y})`.
  have hslice : ∀ y : Rn m,
      ψ '' (B ∩ G ⁻¹' {y}) = ⋃ t, ψ '' (P t ∩ G ⁻¹' {y}) := by
    intro y
    rw [← image_iUnion, ← iUnion_inter, hPU]
  have hslice_meas : ∀ (y : Rn m) t, MeasurableSet (ψ '' (P t ∩ G ⁻¹' {y})) := by
    intro y t
    have hsub : P t ∩ G ⁻¹' {y} ⊆ D := inter_subset_left.trans (hPD t)
    exact ((hPm t).inter (isClosed_singleton.preimage hG).measurableSet).image_of_continuousOn_injOn
      (hψc.mono hsub) (hψi.mono hsub)
  have hslice_disj : ∀ y : Rn m,
      Pairwise (Function.onFun Disjoint fun t ↦ ψ '' (P t ∩ G ⁻¹' {y})) := by
    intro y a b hab
    exact Disjoint.image ((hPd hab).mono inter_subset_left inter_subset_left) hψi
      (inter_subset_left.trans (hPD a)) (inter_subset_left.trans (hPD b))
  have hfun : (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) =
      fun y ↦ ∑' t, ∫⁻ x in ψ '' (P t ∩ G ⁻¹' {y}), φ x ∂μHE[k] := by
    funext y
    rw [hslice y, lintegral_iUnion (hslice_meas y) (hslice_disj y)]
  -- Step 4 (measurability): a countable sum of a.e.-measurable functions.
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact AEMeasurable.tsum fun t ↦ (hPgood t φ hφ).1
  -- Step 5 (identity): countable additivity on the left, goodness of the pieces, `lintegral_tsum`.
  · calc ∫⁻ u in B, φ (ψ u) * w u = ∫⁻ u in ⋃ t, P t, φ (ψ u) * w u := by rw [hPU]
      _ = ∑' t, ∫⁻ u in P t, φ (ψ u) * w u := lintegral_iUnion hPm hPd _
      _ = ∑' t, ∫⁻ y, (∫⁻ x in ψ '' (P t ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
        congr 1
        funext t
        exact (hPgood t φ hφ).2
      _ = ∫⁻ y, ∑' t, (∫⁻ x in ψ '' (P t ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume :=
        (lintegral_tsum fun t ↦ (hPgood t φ hφ).1).symm
      _ = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by rw [hfun]
/-- **Fine covers with small weighted image volume give `Hᵏ`-null slices** (the Fatou covering
criterion behind Simon Ch. 2, p. 66, the consequence of (6.3) stated before 6.4,
`chapter-02.txt` lines 1476–1478). Let `k > 0` and let `S ⊆ ℝⁿ` and `G : ℝⁿ → ℝᵐ` be arbitrary.
If for every `ε > 0` some countable cover `(Tᵢ)` of `S` has `diam Tᵢ ≤ ε` and
`∑ᵢ (diam Tᵢ)ᵏ Lᵐ(G(Tᵢ ∩ S)) ≤ ε`, then `Hᵏ(S ∩ G⁻¹{y}) = 0` for `Lᵐ`-a.e. `y ∈ ℝᵐ`.
With measurable hulls `Aⱼᵢ ⊇ G(Tⱼᵢ ∩ S)` of equal measure, the majorants
`gⱼ = ∑ᵢ (diam Tⱼᵢ)ᵏ 1_{Aⱼᵢ}` have `∫ gⱼ ≤ εⱼ → 0`, so `liminf gⱼ = 0` a.e. by Fatou; for such
`y` the covers `Tⱼᵢ ∩ S ∩ G⁻¹{y}` give `Hᵏ(S ∩ G⁻¹{y}) ≤ liminf gⱼ(y) = 0`. -/
theorem Submission.critSlices_ae_slice_null_of_covers : ∀ (n m k : ℕ) (S : Set (Rn n)) (G : Rn n → Rn m), 0 < k → (∀ ε : ℝ≥0∞, 0 < ε → ∃ (ι : Type) (_ : Countable ι) (T : ι → Set (Rn n)), S ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ ε) ∧ ∑' i, Metric.ediam (T i) ^ k * volume (G '' (T i ∩ S)) ≤ ε) → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (S ∩ G ⁻¹' {y}) = 0 := by
  intro n m k S G hk hcov
  -- Covers at the scales `εⱼ = (j + 1)⁻¹ → 0`.
  have hεpos : ∀ j : ℕ, (0 : ℝ≥0∞) < ((j : ℝ≥0∞) + 1)⁻¹ := fun j =>
    ENNReal.inv_pos.2 (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top j, ENNReal.one_ne_top⟩)
  have hr : Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) :=
    (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)).congr fun j => by
      simp [Nat.cast_add, Nat.cast_one]
  choose ι hι T hTcov hTdiam hTsum using fun j : ℕ => hcov _ (hεpos j)
  -- Measurable hulls `Aⱼᵢ ⊇ G(Tⱼᵢ ∩ S)` of equal measure and the majorants `gⱼ`.
  set A : ∀ j, ι j → Set (Rn m) := fun j i => toMeasurable volume (G '' (T j i ∩ S))
  set g : ℕ → Rn m → ℝ≥0∞ := fun j y => ∑' i, Metric.ediam (T j i) ^ k * (A j i).indicator 1 y
  have hterm : ∀ j i, Measurable fun y => Metric.ediam (T j i) ^ k * (A j i).indicator 1 y :=
    fun j i => measurable_const.mul (measurable_one.indicator (measurableSet_toMeasurable _ _))
  have hgm : ∀ j, Measurable (g j) := fun j => Measurable.tsum fun i => hterm j i
  have hgint : ∀ j, ∫⁻ y, g j y ≤ ((j : ℝ≥0∞) + 1)⁻¹ := by
    intro j
    calc ∫⁻ y, g j y
        = ∑' i, ∫⁻ y, Metric.ediam (T j i) ^ k * (A j i).indicator 1 y :=
          lintegral_tsum fun i => (hterm j i).aemeasurable
      _ = ∑' i, Metric.ediam (T j i) ^ k * volume (G '' (T j i ∩ S)) := by
          congr 1
          ext i
          rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_toMeasurable _ _)),
            lintegral_indicator_one (measurableSet_toMeasurable _ _), measure_toMeasurable]
      _ ≤ ((j : ℝ≥0∞) + 1)⁻¹ := hTsum j
  -- Fatou: `∫ liminf gⱼ ≤ liminf ∫ gⱼ ≤ liminf εⱼ = 0`, so `liminf gⱼ = 0` a.e.
  have hfatou : ∫⁻ y, liminf (fun j => g j y) atTop = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ y, liminf (fun j => g j y) atTop ≤ liminf (fun j => ∫⁻ y, g j y) atTop :=
          lintegral_liminf_le hgm
      _ ≤ liminf (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop :=
          liminf_le_liminf (Eventually.of_forall hgint)
      _ = 0 := hr.liminf_eq
  have hae : ∀ᵐ y ∂(volume : Measure (Rn m)), liminf (fun j => g j y) atTop = 0 := by
    filter_upwards [(lintegral_eq_zero_iff (Measurable.liminf hgm)).1 hfatou] with y hy
    simpa using hy
  filter_upwards [hae] with y hy
  -- The covers `Tⱼᵢ ∩ (S ∩ G⁻¹{y})` of the slice: an empty piece contributes `0ᵏ = 0`, and a
  -- nonempty one forces `y ∈ G(Tⱼᵢ ∩ S) ⊆ Aⱼᵢ`.
  have hH : μH[(k : ℝ)] (S ∩ G ⁻¹' {y}) ≤ liminf (fun j => g j y) atTop := by
    calc μH[(k : ℝ)] (S ∩ G ⁻¹' {y})
        ≤ liminf (fun j => ∑' i, Metric.ediam (T j i ∩ (S ∩ G ⁻¹' {y})) ^ (k : ℝ)) atTop :=
          Measure.hausdorffMeasure_le_liminf_tsum (k : ℝ) (S ∩ G ⁻¹' {y}) _ hr
            (fun j i => T j i ∩ (S ∩ G ⁻¹' {y}))
            (Eventually.of_forall fun j i =>
              (Metric.ediam_mono inter_subset_left).trans (hTdiam j i))
            (Eventually.of_forall fun j u hu => by
              obtain ⟨i, hi⟩ := mem_iUnion.1 (hTcov j hu.1)
              exact mem_iUnion.2 ⟨i, hi, hu⟩)
      _ ≤ liminf (fun j => g j y) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun j => ENNReal.tsum_le_tsum fun i => ?_)
          by_cases hne : (T j i ∩ (S ∩ G ⁻¹' {y})).Nonempty
          · obtain ⟨u, huT, huS, huy⟩ := hne
            have hyA : y ∈ A j i := subset_toMeasurable _ _ ⟨u, ⟨huT, huS⟩, huy⟩
            rw [indicator_of_mem hyA, Pi.one_apply, mul_one, ENNReal.rpow_natCast]
            exact pow_le_pow_left' (Metric.ediam_mono inter_subset_left) k
          · rw [not_nonempty_iff_eq_empty.1 hne, Metric.ediam_empty,
              ENNReal.zero_rpow_of_pos (by exact_mod_cast hk)]
            exact zero_le
  have hμH : μH[(k : ℝ)] (S ∩ G ⁻¹' {y}) = 0 := le_antisymm (hH.trans hy.le) zero_le
  -- `μHE[k] = c_k • μH[k]`.
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hμH, smul_zero]
/-- **Volume of a slab intersected with a ball**: for a unit vector `ν` of `ℝᵐ`,
`Lᵐ{w : |⟨w - c, ν⟩| ≤ r, |w - c| ≤ R} ≤ 2r (2R)^{m-1}`. This is the slab estimate in a direct
covering proof that critical slices are null (Simon Ch. 2, p. 66: the consequence of 6.3 stated
before 6.4, which Simon derives from the co-area formula 6.3, whose proof he defers to [Har79],
[Fed69]). The set is empty if `r < 0` or `R < 0`, and `‖ν‖ = 1` forces `m ≥ 1`. The reflection
`ρ` of `ℝᵐ` in `(ℝ (ν - e₀))ᗮ` maps `ν` to `e₀`, so `w ↦ ρ(w - c)` maps the set into the box
`[-r, r] × [-R, R]^{m-1}`, since `⟨ρ(w - c), e₀⟩ = ⟨w - c, ν⟩` and `|x_i| ≤ |x| = |w - c|`.
Translation, `ρ` and `ofLp` preserve Lebesgue measure, and the box has volume `2r (2R)^{m-1}`. -/
theorem Submission.critSlices_slab_volume_le : ∀ (m : ℕ) (ν c : Rn m) (r R : ℝ), ‖ν‖ = 1 → volume {w : Rn m | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} ≤ ENNReal.ofReal (2 * r * (2 * R) ^ (m - 1)) := by
  intro m ν c r R hν
  -- Step 1: for `r < 0` or `R < 0` the set is empty.
  by_cases hr : r < 0
  · have hempty : {w : Rn m | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h
      exact absurd ((abs_nonneg _).trans h) (not_le.2 hr)
    rw [hempty, measure_empty]
    positivity
  by_cases hR : R < 0
  · have hempty : {w : Rn m | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ h
      exact absurd ((norm_nonneg _).trans h) (not_le.2 hR)
    rw [hempty, measure_empty]
    positivity
  push Not at hr hR
  -- Step 2: `‖ν‖ = 1` rules out `m = 0`.
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    rcases m with _ | m'
    · exfalso
      have h0 : ν = 0 := Subsingleton.elim _ _
      rw [h0, norm_zero] at hν
      exact zero_ne_one hν
    · exact ⟨m', rfl⟩
  -- Step 3: the reflection `ρ` in `(ℝ (ν - e₀))ᗮ` satisfies `ρ ν = e₀`.
  set e₀ : Rn (m' + 1) := EuclideanSpace.single 0 1 with he₀
  have he₀n : ‖e₀‖ = 1 := by simp [he₀]
  set ρ : Rn (m' + 1) ≃ₗᵢ[ℝ] Rn (m' + 1) := (ℝ ∙ (ν - e₀))ᗮ.reflection with hρ
  have hρν : ρ ν = e₀ := Submodule.reflection_sub (hν.trans he₀n.symm)
  -- Step 4: `w ↦ ofLp (ρ (w - c))` maps the set into the box `Icc a b`.
  set a : Fin (m' + 1) → ℝ := fun i ↦ if i = 0 then -r else -R with ha
  set b : Fin (m' + 1) → ℝ := fun i ↦ if i = 0 then r else R with hb
  have hsub : {w : Rn (m' + 1) | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} ⊆
      (WithLp.ofLp ∘ ρ ∘ fun w ↦ w - c) ⁻¹' Icc a b := by
    intro w hw
    obtain ⟨h1, h2⟩ := hw
    simp only [mem_preimage, Function.comp_apply, mem_Icc]
    set x := ρ (w - c) with hx
    have hx0 : x.ofLp 0 = inner ℝ (w - c) ν := by
      have h : inner ℝ x e₀ = x.ofLp 0 := by
        rw [he₀, EuclideanSpace.inner_single_right]
        simp
      rw [← h, ← hρν, hx, LinearIsometryEquiv.inner_map_map]
    have hxn : ‖x‖ = ‖w - c‖ := LinearIsometryEquiv.norm_map _ _
    have hcoord : ∀ i, |x.ofLp i| ≤ R := by
      intro i
      have := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at this
      exact this.trans (hxn ▸ h2)
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · by_cases hi : i = 0
      · subst hi
        simp only [ha, ite_true]
        rw [hx0]
        exact (abs_le.1 h1).1
      · simp only [ha, hi, ite_false]
        exact (abs_le.1 (hcoord i)).1
    · by_cases hi : i = 0
      · subst hi
        simp only [hb, ite_true]
        rw [hx0]
        exact (abs_le.1 h1).2
      · simp only [hb, hi, ite_false]
        exact (abs_le.1 (hcoord i)).2
  -- Step 5: translation, `ρ` and `ofLp` preserve Lebesgue measure.
  have hmp : MeasurePreserving (WithLp.ofLp ∘ ρ ∘ fun w : Rn (m' + 1) ↦ w - c) volume volume :=
    (PiLp.volume_preserving_ofLp (Fin (m' + 1))).comp
      (ρ.measurePreserving.comp (measurePreserving_sub_right volume c))
  -- Steps 6–7: the box has volume `2r (2R)^{m'}`; conclude by monotonicity.
  calc volume {w : Rn (m' + 1) | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R}
      ≤ volume ((WithLp.ofLp ∘ ρ ∘ fun w ↦ w - c) ⁻¹' Icc a b) := measure_mono hsub
    _ = volume (Icc a b) := hmp.measure_preimage measurableSet_Icc.nullMeasurableSet
    _ = ∏ i, ENNReal.ofReal (b i - a i) := Real.volume_Icc_pi
    _ = ENNReal.ofReal (2 * r * (2 * R) ^ (m' + 1 - 1)) := by
      rw [Fin.prod_univ_succ]
      simp only [ha, hb, ite_true, Fin.succ_ne_zero, ite_false, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
      rw [ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_pow (by linarith)]
      congr 2 <;> ring

/-- **Images under a nearly degenerate derivative lie in a thin slab.** This is the step "the
image of a critical subcube lies in a thin slab" of the covering proof that critical slices are
null (Simon Ch. 2, p. 66, the consequence of 6.3, `chapter-02.txt` lines 1476–1478; Simon gives
no proof). Here it is stated for a convex `S` of radius `d` about `u₀`. Since `P` is not
surjective, some unit `ν` is orthogonal to `range P`. The mean value inequality for `G - P` gives
`G(u) - G(u₀) = P(u - u₀) + e` with `|e| ≤ εd`. Hence `G(S)` lies in
`{w : |⟨w - G(u₀), ν⟩| ≤ εd, |w - G(u₀)| ≤ (Λ + ε)d}`, whose volume is bounded by
`Submission.critSlices_slab_volume_le`. -/
theorem Submission.critSlices_image_volume_le_of_fderiv_near : ∀ (n m : ℕ) (G : Rn n → Rn m)
    (S : Set (Rn n)) (P : Rn n →L[ℝ] Rn m) (u₀ : Rn n) (d ε Λ : ℝ), Convex ℝ S → u₀ ∈ S →
    (∀ v ∈ S, DifferentiableAt ℝ G v) → (∀ v ∈ S, ‖fderiv ℝ G v - P‖ ≤ ε) →
    (∀ v ∈ S, ‖v - u₀‖ ≤ d) → ¬ Function.Surjective P → ‖P‖ ≤ Λ →
    volume (G '' S) ≤ ENNReal.ofReal (2 * (ε * d) * (2 * ((Λ + ε) * d)) ^ (m - 1)) := by
  intro n m G S P u₀ d ε Λ hS hu₀ hdiff hnear hd hP hΛ
  -- `u₀ ∈ S` gives `ε ≥ ‖DG(u₀) - P‖ ≥ 0`.
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hnear u₀ hu₀)
  -- A unit normal `ν` to the proper subspace `range P`: `(range P)ᗮ ≠ 0` as `range P ≠ ℝᵐ`.
  obtain ⟨ν, hν, hPν⟩ : ∃ ν : Rn m, ‖ν‖ = 1 ∧ ∀ x, inner ℝ (P x) ν = 0 := by
    have hV : LinearMap.range (P : Rn n →ₗ[ℝ] Rn m) ≠ ⊤ := fun h ↦
      hP fun y ↦ LinearMap.mem_range.1 (h ▸ Submodule.mem_top)
    obtain ⟨ν₀, hν₀, hν₀0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (mt Submodule.orthogonal_eq_bot_iff.1 hV)
    refine ⟨‖ν₀‖⁻¹ • ν₀, ?_, fun x ↦ ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hν₀0)]
    · have h0 : inner ℝ (P x) ν₀ = 0 :=
        (Submodule.mem_orthogonal _ _).1 hν₀ (P x) (LinearMap.mem_range_self _ x)
      rw [inner_smul_right, h0, mul_zero]
  -- `G(S)` lies in the slab of half-width `εd` normal to `ν`, cut off by the closed ball of
  -- radius `(Λ + ε)d`, both about `G(u₀)`.
  have hsub : G '' S ⊆
      {w : Rn m | |inner ℝ (w - G u₀) ν| ≤ ε * d ∧ ‖w - G u₀‖ ≤ (Λ + ε) * d} := by
    rintro _ ⟨u, hu, rfl⟩
    -- Mean value inequality for `G - P` on the convex `S`: `|e| ≤ ε|u - u₀| ≤ εd`.
    set e := G u - G u₀ - P (u - u₀) with he_def
    have he : ‖e‖ ≤ ε * d :=
      (hS.norm_image_sub_le_of_norm_fderiv_le' hdiff hnear hu₀ hu).trans
        (mul_le_mul_of_nonneg_left (hd u hu) hε)
    have hw : G u - G u₀ = P (u - u₀) + e := by
      rw [he_def]
      abel
    refine ⟨?_, ?_⟩
    · -- `⟨w, ν⟩ = ⟨e, ν⟩` because `ν ⊥ range P`; then Cauchy–Schwarz.
      rw [hw, inner_add_left, hPν, zero_add]
      calc |inner ℝ e ν| ≤ ‖e‖ * ‖ν‖ := abs_real_inner_le_norm e ν
        _ = ‖e‖ := by rw [hν, mul_one]
        _ ≤ ε * d := he
    · -- `|w| ≤ ‖P‖ |u - u₀| + |e| ≤ Λd + εd`.
      rw [hw]
      calc ‖P (u - u₀) + e‖ ≤ ‖P (u - u₀)‖ + ‖e‖ := norm_add_le _ _
        _ ≤ Λ * d + ε * d := add_le_add ((P.le_opNorm _).trans
            (mul_le_mul hΛ (hd u hu) (norm_nonneg _) ((norm_nonneg _).trans hΛ))) he
        _ = (Λ + ε) * d := by ring
  calc volume (G '' S)
      ≤ volume {w : Rn m | |inner ℝ (w - G u₀) ν| ≤ ε * d ∧ ‖w - G u₀‖ ≤ (Λ + ε) * d} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * (ε * d) * (2 * ((Λ + ε) * d)) ^ (m - 1)) :=
        Submission.critSlices_slab_volume_le m ν (G u₀) (ε * d) ((Λ + ε) * d) hν
/-- **Subdivision of `[-R, R]ⁿ` into `Mⁿ` subcubes**: for `M > 0` and `R ≥ 0`, with side
`s = 2R/M`, the closed cubes `Q_α = {u : -R + s αᵢ ≤ uᵢ ≤ -R + s (αᵢ + 1) for all i}`,
`α : Fin n → Fin M`, are convex, lie in `closedBall 0 (√n R)`, have diameter at most `√n s` and
cover `closedBall 0 R`. This is the cube subdivision in the covering proof that critical slices
are null (Simon Ch. 2, p. 66, the consequence of (6.3) stated before 6.4). The defining
inequalities are preserved by convex combinations. Every coordinate of a point of `Q_α` lies in
`[-R, R]`, and two points of `Q_α` differ by at most `s` in every coordinate, which gives the two
norm bounds. A point `u` of `closedBall 0 R` has `|uᵢ| ≤ R`; it lies in `Q_α` for `α ≡ 0` if
`R = 0`, and for `αᵢ = min ⌊(uᵢ + R)/s⌋₊ (M - 1)` if `R > 0`. -/
theorem Submission.critSlices_cube_cover : ∀ (n M : ℕ) (R : ℝ), 0 < M → 0 ≤ R → ∃ Q : (Fin n → Fin M) → Set (Rn n), (∀ α, Convex ℝ (Q α)) ∧ (∀ α, Q α ⊆ Metric.closedBall 0 (Real.sqrt n * R)) ∧ (∀ α, ∀ u ∈ Q α, ∀ v ∈ Q α, dist u v ≤ Real.sqrt n * (2 * R / M)) ∧ Metric.closedBall (0 : Rn n) R ⊆ ⋃ α, Q α := by
  intro n M R hM hR
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  -- The side length `s = 2R/M`, so `s ≥ 0` and `s M = 2R`.
  set s : ℝ := 2 * R / M with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hM'.le
  have hsM : s * M = 2 * R := div_mul_cancel₀ _ hM'.ne'
  refine ⟨fun α ↦ {u : Rn n | ∀ i, -R + s * (α i : ℕ) ≤ u i ∧ u i ≤ -R + s * ((α i : ℕ) + 1)},
    ?_, ?_, ?_, ?_⟩
  -- Step 1: the defining inequalities are preserved by convex combinations.
  · intro α u hu v hv a b ha hb hab i
    obtain ⟨hu1, hu2⟩ := hu i
    obtain ⟨hv1, hv2⟩ := hv i
    obtain rfl : b = 1 - a := by linarith
    have hcomb : (a • u + (1 - a) • v) i = a * u i + (1 - a) * v i := rfl
    rw [hcomb]
    constructor
    · linarith [mul_le_mul_of_nonneg_left hu1 ha, mul_le_mul_of_nonneg_left hv1 hb]
    · linarith [mul_le_mul_of_nonneg_left hu2 ha, mul_le_mul_of_nonneg_left hv2 hb]
  -- Step 2: the coordinates of a point of `Q α` lie in `[-R, R]`, so its norm is at most `√n R`.
  · intro α u hu
    have hcoord : ∀ i, ‖u i‖ ≤ R := by
      intro i
      obtain ⟨h1, h2⟩ := hu i
      have hα0 : (0 : ℝ) ≤ (α i : ℕ) := Nat.cast_nonneg _
      have hαM : ((α i : ℕ) : ℝ) + 1 ≤ M := by exact_mod_cast (α i).isLt
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [mul_nonneg hs0 hα0]
      · linarith [mul_le_mul_of_nonneg_left hαM hs0]
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    calc √(∑ i, ‖u i‖ ^ 2) ≤ √(∑ _i : Fin n, R ^ 2) := by
          gcongr with i
          exact hcoord i
      _ = √n * R := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hR]
  -- Step 3: two points of `Q α` differ by at most `s` in every coordinate.
  · intro α u hu v hv
    have hcoord : ∀ i, dist (u i) (v i) ≤ s := by
      intro i
      obtain ⟨hu1, hu2⟩ := hu i
      obtain ⟨hv1, hv2⟩ := hv i
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith
    rw [EuclideanSpace.dist_eq]
    calc √(∑ i, dist (u i) (v i) ^ 2) ≤ √(∑ _i : Fin n, s ^ 2) := by
          gcongr with i
          exact hcoord i
      _ = √n * s := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hs0]
  -- Step 4: every point of `closedBall 0 R` lies in some `Q α`.
  · intro u hu
    rw [mem_closedBall_zero_iff] at hu
    have hcoord : ∀ i, |u i| ≤ R := fun i ↦ by
      have h := PiLp.norm_apply_le u i
      rw [Real.norm_eq_abs] at h
      exact h.trans hu
    rcases hR.eq_or_lt with rfl | hRpos
    · -- `R = 0`: all coordinates vanish and `s = 0`; take `α ≡ 0`.
      refine mem_iUnion.2 ⟨fun _ ↦ ⟨0, hM⟩, fun i ↦ ?_⟩
      have hui : u i = 0 := abs_nonpos_iff.1 (hcoord i)
      have hs00 : s = 0 := by rw [hs]; simp
      simp [hui, hs00]
    · -- `R > 0`: `αᵢ = min ⌊tᵢ⌋₊ (M - 1)` with `tᵢ = (uᵢ + R)/s ∈ [0, M]`.
      have hspos : 0 < s := div_pos (by linarith) hM'
      obtain ⟨t, ht⟩ : ∃ t : Fin n → ℝ, ∀ i, t i = (u i + R) / s := ⟨_, fun _ ↦ rfl⟩
      have ht0 : ∀ i, 0 ≤ t i := fun i ↦ by
        rw [ht i]
        exact div_nonneg (by linarith [(abs_le.1 (hcoord i)).1]) hs0
      have htM : ∀ i, t i ≤ M := fun i ↦ by
        rw [ht i, div_le_iff₀ hspos]
        linarith [(abs_le.1 (hcoord i)).2]
      have hk : ∀ i, ((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) ≤ t i ∧
          t i ≤ ((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) + 1 := by
        intro i
        refine ⟨(Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le (ht0 i)), ?_⟩
        rcases le_total ⌊t i⌋₊ (M - 1) with hle | hle
        · rw [min_eq_left hle]
          exact (Nat.lt_floor_add_one (t i)).le
        · rw [min_eq_right hle, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hM.ne'), Nat.cast_one,
            sub_add_cancel]
          exact htM i
      refine mem_iUnion.2 ⟨fun i ↦ ⟨min ⌊t i⌋₊ (M - 1), by omega⟩, fun i ↦ ?_⟩
      obtain ⟨hk1, hk2⟩ := hk i
      have hut : u i = -R + s * t i := by
        rw [ht i, mul_div_cancel₀ _ hspos.ne']
        ring
      show -R + s * ((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) ≤ u i ∧
        u i ≤ -R + s * (((min ⌊t i⌋₊ (M - 1) : ℕ) : ℝ) + 1)
      rw [hut]
      exact ⟨by linarith [mul_le_mul_of_nonneg_left hk1 hs0],
        by linarith [mul_le_mul_of_nonneg_left hk2 hs0]⟩

/-- **`C¹` critical slices are `Hᵏ`-null** (Simon Ch. 2, p. 66: the consequence of the co-area
formula 6.3 stated before Theorem 6.4, `chapter-02.txt` lines 1476–1478, whose proof Simon leaves
to [Har79]/[Fed69]). Let `G : ℝ^{m+k} → ℝᵐ` be `C¹`, `k > 0` and `C = {u : DG(u) not surjective}`.
Then `Hᵏ(C ∩ G⁻¹{y}) = 0` for `Lᵐ`-a.e. `y`. If `m = 0` then `C = ∅`. Otherwise, by the fine-cover
criterion, it suffices to treat `C ∩ B̄_R` for `R ∈ ℕ`. Given `ε > 0`, let `Λ` bound `‖DG‖` on
`K = B̄_{√n R}` (`n = m + k`), let `η > 0` be small and `δ > 0` such that
`‖DG(v) - DG(v')‖ ≤ η` for `v, v' ∈ K` with `|v - v'| ≤ δ`, and subdivide `[-R, R]ⁿ` into `Mⁿ`
convex cubes `Q` of diameter `d ≤ min(δ, ε)`. If `Q` meets `C` at `u₀`, then `G(Q)` lies in a slab
normal to `range DG(u₀)`, so `Lᵐ(G(Q)) ≤ 2ηd (2(Λ + η)d)^{m-1}`. As `Md = 2√n R`, the cover has
`Σ_Q (diam Q)ᵏ Lᵐ(G(Q ∩ C)) ≤ (2√n R)ⁿ 2ᵐ (Λ + 1)^{m-1} η ≤ ε`. -/
theorem Submission.c1_critical_slices_null : ∀ (m k : ℕ) (G : Rn (m + k) → Rn m), 0 < k →
    ContDiff ℝ 1 G → ∀ᵐ y ∂(volume : Measure (Rn m)),
      μHE[k] ({u | ¬ Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}) = 0 := by
  intro m k G hk hG
  -- `m = 0`: every linear map into `ℝ⁰` is surjective, so the critical set is empty.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hC : {u : Rn (0 + k) | ¬ Function.Surjective (fderiv ℝ G u)} = ∅ := by
      ext u
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
      exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
    filter_upwards with y
    simp [hC]
  set C := {u : Rn (m + k) | ¬ Function.Surjective (fderiv ℝ G u)} with hCdef
  have hdiff : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  -- `m ≥ 1`: by the fine-cover criterion, each `C ∩ B̄_R` (`R ∈ ℕ`) has `Hᵏ`-null slices over
  -- `Lᵐ`-a.e. `y`.
  have key : ∀ R : ℕ, ∀ᵐ y ∂(volume : Measure (Rn m)),
      μHE[k] ((C ∩ Metric.closedBall 0 (R : ℝ)) ∩ G ⁻¹' {y}) = 0 := by
    intro R
    refine Submission.critSlices_ae_slice_null_of_covers (m + k) m k
      (C ∩ Metric.closedBall 0 (R : ℝ)) G hk fun ε hε ↦ ?_
    -- Constants: `0 < e` with `e ≤ ε`; a bound `Λ ≥ 0` of `‖DG‖` on the compact `K = B̄_{√n R}`;
    -- the tolerance `η ∈ (0, 1]` with `A₀ η ≤ e`; the modulus `δ > 0` of uniform continuity of
    -- `DG` on `K` for `η`; and `M ∈ ℕ` with cube diameter `d = √n (2R / M) ≤ min(δ, e)`.
    obtain ⟨e, he0, he⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
      obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
      exact ⟨r, ENNReal.ofReal_pos.1 hr, hrε.le⟩
    set K := Metric.closedBall (0 : Rn (m + k)) (Real.sqrt ((m + k : ℕ) : ℝ) * R) with hKdef
    have hK : IsCompact K := isCompact_closedBall _ _
    obtain ⟨Λ₀, hΛ₀⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    set Λ : ℝ := max Λ₀ 0 with hΛdef
    have hΛ : ∀ x ∈ K, ‖fderiv ℝ G x‖ ≤ Λ := fun x hx ↦ (hΛ₀ x hx).trans (le_max_left _ _)
    have hΛ0 : 0 ≤ Λ := le_max_right _ _
    set A₀ : ℝ := (2 * Real.sqrt ((m + k : ℕ) : ℝ) * R) ^ (m + k) * 2 ^ m * (Λ + 1) ^ (m - 1)
      with hA₀def
    have hA₀ : 0 ≤ A₀ := by positivity
    set η : ℝ := min 1 (e / (A₀ + 1)) with hηdef
    have hη0 : 0 < η := lt_min one_pos (div_pos he0 (by linarith))
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηA : A₀ * η ≤ e := by
      have h1 : A₀ * η ≤ A₀ * (e / (A₀ + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hA₀
      have h2 : A₀ * (e / (A₀ + 1)) ≤ e := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.1
      (hK.uniformContinuousOn_of_continuous hcont.continuousOn) η hη0
    set ρ : ℝ := min δ e with hρdef
    have hρ0 : 0 < ρ := lt_min hδ0 he0
    obtain ⟨M, hM⟩ := exists_nat_gt (2 * Real.sqrt ((m + k : ℕ) : ℝ) * R / ρ)
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    have hMpos' : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hM
    have hMpos : 0 < M := by exact_mod_cast hMpos'
    set d : ℝ := Real.sqrt ((m + k : ℕ) : ℝ) * (2 * R / M) with hddef
    have hd0 : 0 ≤ d := by positivity
    have hdρ : d ≤ ρ := by
      have h := (div_lt_iff₀ hρ0).1 hM
      rw [hddef, mul_div_assoc', div_le_iff₀ hMpos']
      nlinarith
    have hdδ : d ≤ δ := hdρ.trans (min_le_left _ _)
    have hde : d ≤ e := hdρ.trans (min_le_right _ _)
    -- The cover: the `Mⁿ` convex cubes `Q α ⊆ K` of diameter `≤ d ≤ ε` covering `B̄_R`.
    obtain ⟨Q, hQconv, hQK, hQdiam, hQcov⟩ :=
      Submission.critSlices_cube_cover (m + k) M R hMpos hR0
    have hdiamQ : ∀ α, Metric.ediam (Q α) ≤ ENNReal.ofReal d := fun α ↦
      Metric.ediam_le fun u hu v hv ↦ by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (hQdiam α u hu v hv)
    refine ⟨Fin (m + k) → Fin M, inferInstance, Q, inter_subset_right.trans hQcov,
      fun α ↦ (hdiamQ α).trans ((ENNReal.ofReal_le_ofReal hde).trans he), ?_⟩
    rw [tsum_fintype]
    -- A cube `Q α` meeting `C` at `u₀`: `‖DG(v) - DG(u₀)‖ ≤ η` and `|v - u₀| ≤ d` on `Q α`, and
    -- `DG(u₀)` is not surjective, so `Lᵐ(G(Q α)) ≤ 2ηd (2(Λ + η)d)^{m-1}`.
    have hterm : ∀ α, Metric.ediam (Q α) ^ k *
        volume (G '' (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ)))) ≤
        ENNReal.ofReal (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1))) := by
      intro α
      by_cases hne : (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ))).Nonempty
      · obtain ⟨u₀, hu₀Q, hu₀C, -⟩ := hne
        have hu₀K : u₀ ∈ K := hQK α hu₀Q
        have hvol := Submission.critSlices_image_volume_le_of_fderiv_near (m + k) m G (Q α)
          (fderiv ℝ G u₀) u₀ d η Λ (hQconv α) hu₀Q (fun v _ ↦ hdiff v)
          (fun v hv ↦ by
            have h := hδ v (hQK α hv) u₀ hu₀K ((hQdiam α v hv u₀ hu₀Q).trans hdδ)
            rwa [dist_eq_norm] at h)
          (fun v hv ↦ by
            rw [← dist_eq_norm]
            exact hQdiam α v hv u₀ hu₀Q)
          hu₀C (hΛ u₀ hu₀K)
        calc Metric.ediam (Q α) ^ k * volume (G '' (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ))))
            ≤ ENNReal.ofReal d ^ k * volume (G '' Q α) :=
              mul_le_mul' (pow_le_pow_left' (hdiamQ α) k)
                (measure_mono (image_mono inter_subset_left))
          _ ≤ ENNReal.ofReal d ^ k *
              ENNReal.ofReal (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1)) :=
              mul_le_mul' le_rfl hvol
          _ = ENNReal.ofReal (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1))) := by
              rw [ENNReal.ofReal_mul (pow_nonneg hd0 k), ENNReal.ofReal_pow hd0]
      · rw [not_nonempty_iff_eq_empty.1 hne, image_empty, measure_empty, mul_zero]
        positivity
    -- Summing over the `Mⁿ` cubes: `Md = 2√n R`, `n = m + k`, `m ≥ 1` and `η ≤ 1` give
    -- `Σ ≤ (2√n R)ⁿ 2ᵐ (Λ + η)^{m-1} η ≤ A₀ η ≤ e ≤ ε`.
    calc ∑ α, Metric.ediam (Q α) ^ k * volume (G '' (Q α ∩ (C ∩ Metric.closedBall 0 (R : ℝ))))
        ≤ ∑ _α : Fin (m + k) → Fin M,
            ENNReal.ofReal (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1))) :=
          Finset.sum_le_sum fun α _ ↦ hterm α
      _ = ENNReal.ofReal ((M : ℝ) ^ (m + k) *
            (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m - 1)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ (m + k)),
            ← Nat.cast_pow, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal e := by
          apply ENNReal.ofReal_le_ofReal
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
          have hMd : (M : ℝ) * d = 2 * Real.sqrt ((m' + 1 + k : ℕ) : ℝ) * R := by
            rw [hddef]
            field_simp
          have hpow : (Λ + η) ^ (m' + 1 - 1) ≤ (Λ + 1) ^ (m' + 1 - 1) :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
          have hid : (M : ℝ) ^ (m' + 1 + k) *
              (d ^ k * (2 * (η * d) * (2 * ((Λ + η) * d)) ^ (m' + 1 - 1))) =
              ((M : ℝ) * d) ^ (m' + 1 + k) * 2 ^ (m' + 1) * (Λ + η) ^ (m' + 1 - 1) * η := by
            simp only [Nat.add_sub_cancel, mul_pow]
            ring
          rw [hid, hMd]
          calc (2 * Real.sqrt ((m' + 1 + k : ℕ) : ℝ) * R) ^ (m' + 1 + k) * 2 ^ (m' + 1) *
                (Λ + η) ^ (m' + 1 - 1) * η
              ≤ (2 * Real.sqrt ((m' + 1 + k : ℕ) : ℝ) * R) ^ (m' + 1 + k) * 2 ^ (m' + 1) *
                (Λ + 1) ^ (m' + 1 - 1) * η := by gcongr
            _ = A₀ * η := by rw [hA₀def]
            _ ≤ e := hηA
      _ ≤ ε := he
  -- `C ∩ G⁻¹{y} ⊆ ⋃_R (C ∩ B̄_R) ∩ G⁻¹{y}`, a countable union of `Hᵏ`-null sets for a.e. `y`.
  filter_upwards [ae_all_iff.2 key] with y hy
  refine measure_mono_null (fun u hu ↦ ?_) (measure_iUnion_null hy)
  obtain ⟨R, hR⟩ := exists_nat_ge ‖u‖
  exact mem_iUnion.2 ⟨R, ⟨hu.1, mem_closedBall_zero_iff.2 hR⟩, hu.2⟩

/-- **`C¹` co-area formula in parameter form** (Simon Ch. 2, 6.3 and 6.6, pp. 66–67, whose proof
Simon omits; [Fed69, 3.2.12, 3.2.22], Evans–Gariepy §3.4), transported by a `C¹` map `ψ` that is
injective on the open `D ⊆ ℝ^{m+k}`. Let `G : ℝ^{m+k} → ℝᵐ` be `C¹`, `K(u) = ker DG(u)` and
`J(u) = normDet(Dψ(u) ∘ ι_{K(u)}) · normDet(DG(u)*)`. Then for every Borel `B ⊆ D` and Borel
`φ ≥ 0`, `y ↦ ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ` is `Lᵐ`-a.e. measurable and
`∫_B φ(ψ(u)) J(u) dLⁿ(u) = ∫_{ℝᵐ} ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ dLᵐ(y)`.
Both claims are glued (Lindelöf, countable additivity) from two kinds of Borel pieces. On the
critical set `Z = {u | DG(u) not surjective}`, `J = 0`, and the slices `Z ∩ G⁻¹{y}` are `Hᵏ`-null
for `Lᵐ`-a.e. `y` (this uses `0 < k`); so both sides vanish. Each `p ∈ D ∖ Z` has an
implicit-function chart `Φ = (G, π)` with source in `D`. On that source the formula follows from
the injective area formula on the slices, the flat Jacobian identity, Tonelli on `ℝᵐ × ℝᵏ` and the
change of variables for `Φ`. -/
theorem Submission.c1_parametric_coarea_formula : ∀ (m k N : ℕ) (D : Set (Rn (m + k)))
    (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m), 0 < m → 0 < k → IsOpen D →
    ContDiffOn ℝ 1 ψ D → InjOn ψ D → ContDiff ℝ 1 G → ∀ B ⊆ D, MeasurableSet B →
    ∀ φ : Rn N → ℝ≥0∞, Measurable φ →
      AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧
        ∫⁻ u in B, φ (ψ u) * ENNReal.ofReal
            (((fderiv ℝ ψ u).toLinearMap ∘ₗ
                (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet *
              (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet) =
          ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume := by
  intro m k N D ψ G _hm hk hD hψ hinj hG
  -- Glue over `Z = {DG not surjective}` with the weight `w = ofReal ∘ J`.
  refine Submission.pcoarea_gluing (m + k) N m k D {u | ¬ Function.Surjective (fderiv ℝ G u)} ψ G
    (fun u ↦ ENNReal.ofReal
      (((fderiv ℝ ψ u).toLinearMap ∘ₗ (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet *
        (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet))
    hD hψ.continuousOn hinj hG.continuous ?_ ?_
  · -- Critical pieces: `J = 0`, and the slices of `Z` are `Hᵏ`-null for `Lᵐ`-a.e. `y`.
    exact Submission.pcoarea_critical_part m k N D ψ G hD hψ
      (Submission.c1_critical_slices_null m k G hk hG)
  · -- Regular pieces: the source of an implicit-function chart at `p ∈ D ∖ Z`, inside `D`.
    intro p hpD hpZ
    obtain ⟨Φ, hpΦ, hsrc, hΦ, hΦs, hfst⟩ :=
      Submission.pcoarea_implicit_chart m k G D p hD hpD hG (not_not.mp hpZ)
    refine ⟨Φ.source, Φ.open_source, hpΦ, fun B hB hBm φ hφ ↦ ?_⟩
    exact Submission.pcoarea_formula_on_chart m k N ψ G Φ (hψ.mono hsrc) (hinj.mono hsrc) hΦ hΦs
      hfst B (hB.trans inter_subset_right) hBm φ hφ
/-- **`normDet` of an adjoint** (Simon Ch. 2, §6, co-area formula for linear maps,
`chapter-02.txt` lines 1424–1461, and Ch. 3 (2.7), `chapter-03.txt` lines 412–419): for a linear
map `P : X → Y` of finite-dimensional real inner product spaces, if `P` is surjective then
`normDet P* = normDet (P ∘ ι)` with `ι` the inclusion of `(ker P)ᗮ`, and otherwise
`normDet P* = 0`. The horizontal map `h = P ∘ ι` is an isomorphism, `P*` corestricts to `h*`
(as `range P* = (ker P)ᗮ`), and in orthonormal bases with a common index the matrix of `h*` is
the transpose of that of `h`. If `P` is not surjective, `ker P* = (range P)ᗮ ≠ 0`. -/
theorem Submission.coarea_normDet_adjoint_eq_horizontal : ∀ {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] (P : X →ₗ[ℝ] Y), (Function.Surjective P → (LinearMap.adjoint P).normDet = (P ∘ₗ (LinearMap.ker P)ᗮ.subtype).normDet) ∧ (¬ Function.Surjective P → (LinearMap.adjoint P).normDet = 0) := by
  intro X Y _ _ _ _ _ _ P
  refine ⟨fun hP => ?_, fun hP => ?_⟩
  · set H := (LinearMap.ker P)ᗮ
    set h : H →ₗ[ℝ] Y := P ∘ₗ H.subtype with hh
    -- `h` is injective, as `ker P ⊓ (ker P)ᗮ = ⊥`.
    have hinj : Function.Injective h := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro u hu
      have hz : (u : X) ∈ LinearMap.ker P ⊓ H := ⟨hu, u.property⟩
      rw [Submodule.inf_orthogonal_eq_bot] at hz
      exact (Submodule.mem_bot ℝ).mpr (Subtype.ext ((Submodule.mem_bot ℝ).mp hz))
    -- `h` is surjective: `P x = h (x - π x)` with `π` the orthogonal projection onto `ker P`.
    have hsurj : Function.Surjective h := by
      intro y
      obtain ⟨x, rfl⟩ := hP y
      refine ⟨⟨x - (LinearMap.ker P).starProjection x,
        Submodule.sub_starProjection_mem_orthogonal x⟩, ?_⟩
      simp [hh, (LinearMap.mem_ker).mp ((LinearMap.ker P).starProjection_apply_mem x)]
    have hd : finrank ℝ H = finrank ℝ Y := (LinearEquiv.ofBijective h ⟨hinj, hsurj⟩).finrank_eq
    -- `P*` takes values in `H = (ker P)ᗮ = range P*`, and its corestriction to `H` is `h*`.
    have hm : ∀ y, LinearMap.adjoint P y ∈ H := by
      intro y
      rw [show H = LinearMap.range (LinearMap.adjoint P) from LinearMap.orthogonal_ker P]
      exact ⟨y, rfl⟩
    have ha : (LinearMap.adjoint P).codRestrict H hm = LinearMap.adjoint h := by
      apply (LinearMap.eq_adjoint_iff _ _).mpr
      intro y u
      exact LinearMap.adjoint_inner_left P (u : X) y
    rw [← LinearMap.normDet_codRestrict hm, ha]
    -- In orthonormal bases indexed by the same `Fin d`, the matrix of `h*` is `Mᴴ = Mᵀ`.
    classical
    let bH := stdOrthonormalBasis ℝ H
    let bY := (stdOrthonormalBasis ℝ Y).reindex (finCongr hd.symm)
    rw [(LinearMap.adjoint h).normDet_eq_norm_det_toMatrix bY bH,
      h.normDet_eq_norm_det_toMatrix bH bY, LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
    simp
  · -- `ker P* = (range P)ᗮ ≠ ⊥`, since `range P ≠ ⊤`.
    rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot, ← LinearMap.orthogonal_range, ne_eq,
      Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]
    exact hP
/-- **Block-triangular factorization of `normDet`** (step 5 of the parent proof of
`coarea_normDet_chain_rule`, the block form of `A`). Let `f : V → X` be a linear bijection,
`K ⊆ V` a subspace and `W = f(K)ᗮ`. In orthonormal bases of `V = K ⊕ Kᗮ` and `X = f(K) ⊕ W`
indexed by `Fin r ⊕ Fin s` (`r = dim K = dim f(K)`, `s = dim Kᗮ = dim W`), the matrix of `f` is
`fromBlocks M₁₁ M₁₂ 0 M₂₂`: `M₁₁` is the matrix of `f|_K : K → f(K)`, the lower-left block
vanishes because `W ⊥ f(K)`, and `M₂₂` is the matrix of `p_W ∘ f ∘ ι_{Kᗮ}` because
`⟪w, x⟫ = ⟪w, p_W x⟫` for `w ∈ W`. Hence `normDet f = |det M₁₁| · |det M₂₂|`, and
`|det M₁₁| = normDet (f ∘ ι_K)` since corestricting to `f(K)` does not change `normDet`. -/
theorem Submission.coarea_normDet_block_triangular : ∀ {V X : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] (f : V →ₗ[ℝ] X) (K : Submodule ℝ V) (W : Submodule ℝ X), Function.Bijective f → W = (K.map f)ᗮ → f.normDet = (f ∘ₗ K.subtype).normDet * ((W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ f ∘ₗ Kᗮ.subtype).normDet := by
  intro V X _ _ _ _ _ _ f K W hf hW
  classical
  -- Notation: `F = f(K)`, so `W = Fᗮ`.
  obtain ⟨F, hF⟩ : ∃ F : Submodule ℝ X, F = K.map f := ⟨_, rfl⟩
  rw [← hF] at hW
  -- Step 1: dimensions, `dim F = dim K` and `dim W = dim Kᗮ`.
  have hr : finrank ℝ F = finrank ℝ K := by
    rw [hF]; exact (Submodule.equivMapOfInjective f hf.1 K).finrank_eq.symm
  have hVX : finrank ℝ V = finrank ℝ X := (LinearEquiv.ofBijective f hf).finrank_eq
  have e1 := Submodule.finrank_add_finrank_orthogonal K
  have e2 := Submodule.finrank_add_finrank_orthogonal F
  rw [← hW] at e2
  have hs : finrank ℝ W = finrank ℝ Kᗮ := by omega
  -- Steps 2–3: orthonormal bases of `K`, `Kᗮ`, `F`, `W`; adapted bases `β` of `V`, `γ` of `X`.
  let b₁ := stdOrthonormalBasis ℝ K
  let b₂ := stdOrthonormalBasis ℝ Kᗮ
  let c₁ : OrthonormalBasis (Fin (finrank ℝ K)) ℝ F :=
    (stdOrthonormalBasis ℝ F).reindex (finCongr hr)
  let c₂ : OrthonormalBasis (Fin (finrank ℝ Kᗮ)) ℝ W :=
    (stdOrthonormalBasis ℝ W).reindex (finCongr hs)
  let c₂' : OrthonormalBasis (Fin (finrank ℝ Kᗮ)) ℝ Fᗮ := c₂.map (LinearIsometryEquiv.ofEq _ _ hW)
  let β := (b₁.prod b₂).map K.orthogonalDecomposition.symm
  let γ := (c₁.prod c₂').map F.orthogonalDecomposition.symm
  have hβl : ∀ i, β (Sum.inl i) = (b₁ i : V) := by intro i; simp [β]
  have hβr : ∀ j, β (Sum.inr j) = (b₂ j : V) := by intro j; simp [β]
  have hγl : ∀ i, γ (Sum.inl i) = (c₁ i : X) := by intro i; simp [γ]
  have hγr : ∀ j, γ (Sum.inr j) = (c₂ j : X) := by intro j; simp [γ, c₂']
  -- The diagonal blocks: `f_K : K → F` and `g = p_W ∘ f ∘ ι_{Kᗮ} : Kᗮ → W`.
  have hmemF : ∀ k : K, f k ∈ F := fun k => hF ▸ Submodule.mem_map_of_mem k.2
  let fK : K →ₗ[ℝ] F := (f ∘ₗ K.subtype).codRestrict F (fun k => hmemF k)
  let g : Kᗮ →ₗ[ℝ] W := (W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ f ∘ₗ Kᗮ.subtype
  -- Steps 6–7: `normDet = |det|` in square orthonormal bases; `normDet (f ∘ ι_K) = normDet f_K`.
  have h1 : (f ∘ₗ K.subtype).normDet = fK.normDet := (LinearMap.normDet_codRestrict _).symm
  rw [h1, LinearMap.normDet_eq_norm_det_toMatrix f β γ,
    LinearMap.normDet_eq_norm_det_toMatrix fK b₁ c₁, LinearMap.normDet_eq_norm_det_toMatrix g b₂ c₂,
    ← norm_mul]
  congr 1
  -- Step 4: the matrix of `f` in `β`, `γ` is block upper triangular.
  have hM : LinearMap.toMatrix β.toBasis γ.toBasis f =
      Matrix.fromBlocks (LinearMap.toMatrix b₁.toBasis c₁.toBasis fK)
        (Matrix.of fun i j => inner ℝ (c₁ i : X) (f (b₂ j))) 0
        (LinearMap.toMatrix b₂.toBasis c₂.toBasis g) := by
    ext a b
    rcases a with i | i <;> rcases b with j | j
    · -- (a) the `K → F` block is the matrix of `f_K`.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₁₁,
        hβl, hγl]
      rfl
    · -- (d) the unconstrained block `M₁₂`.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₁₂,
        hβr, hγl, Matrix.of_apply]
    · -- (b) `W ⊥ F` kills the `K → W` block.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₂₁,
        hβl, hγr, Matrix.zero_apply]
      have hmem : (c₂ i : X) ∈ Fᗮ := hW ▸ (c₂ i).2
      exact Submodule.inner_left_of_mem_orthogonal (hmemF (b₁ j)) hmem
    · -- (c) `⟪w, x⟫ = ⟪w, p_W x⟫` for `w ∈ W`: the `Kᗮ → W` block is the matrix of `g`.
      simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, Matrix.fromBlocks_apply₂₂,
        hβr, hγr]
      simp [g]
  -- Step 5: `det (fromBlocks M₁₁ M₁₂ 0 M₂₂) = det M₁₁ * det M₂₂`.
  rw [hM, Matrix.det_fromBlocks_zero₂₁]
/-- **Horizontal step of the `normDet` chain rule** (step 6 of the supplied proof of the `normDet`
chain rule behind the co-area Jacobian, Simon Ch. 3, (2.7)). Let `B : V → X` be bijective,
`Γ = L ∘ B`, `K = ker Γ` and `W = (ker L)ᗮ`. Since `Wᗮ = ker L`, the restriction of `Γ` to `Kᗮ`
factors as `L|_W ∘ (p_W ∘ B|_{Kᗮ})`, and `B(K) = ker L` gives `dim Kᗮ = dim W`; hence
`normDet (Γ|_{Kᗮ}) = normDet (L|_W) · normDet (p_W ∘ B|_{Kᗮ})`. -/
theorem Submission.coarea_normDet_horizontal_comp : ∀ {V X Y : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] (B : V →ₗ[ℝ] X) (L : X →ₗ[ℝ] Y) (Γ : V →ₗ[ℝ] Y) (K : Submodule ℝ V) (W : Submodule ℝ X), Function.Bijective B → (∀ v, Γ v = L (B v)) → K = LinearMap.ker Γ → W = (LinearMap.ker L)ᗮ → (Γ ∘ₗ Kᗮ.subtype).normDet = (L ∘ₗ W.subtype).normDet * ((W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ B ∘ₗ Kᗮ.subtype).normDet := by
  intro V X Y _ _ _ _ _ _ _ _ _ B L Γ K W hB hΓ hK hW
  -- `Wᗮ = (ker L)ᗮᗮ = ker L`.
  have hWperp : Wᗮ = LinearMap.ker L := by
    rw [hW, Submodule.orthogonal_orthogonal]
  -- `Γ ∘ ι_{Kᗮ} = (L ∘ ι_W) ∘ (p_W ∘ B ∘ ι_{Kᗮ})`, since `B u - p_W (B u) ∈ Wᗮ = ker L`.
  have hcomp : Γ ∘ₗ Kᗮ.subtype =
      (L ∘ₗ W.subtype) ∘ₗ ((W.orthogonalProjectionOnto : X →ₗ[ℝ] W) ∘ₗ B ∘ₗ Kᗮ.subtype) := by
    refine LinearMap.ext fun u ↦ ?_
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
    have h : B u - (W.orthogonalProjectionOnto (B u) : X) ∈ Wᗮ :=
      Submodule.sub_starProjection_mem_orthogonal (K := W) (B u)
    rw [hWperp, LinearMap.mem_ker, map_sub, sub_eq_zero] at h
    rw [hΓ]
    exact h
  -- `ker L = B(K)`, using that `B` is surjective.
  have hker : LinearMap.ker L = K.map B := by
    ext t
    constructor
    · intro ht
      obtain ⟨v, rfl⟩ := hB.2 t
      refine ⟨v, ?_, rfl⟩
      rw [SetLike.mem_coe, hK, LinearMap.mem_ker, hΓ]
      exact LinearMap.mem_ker.mp ht
    · rintro ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, hK, LinearMap.mem_ker, hΓ] at hv
      exact hv
  -- `dim Kᗮ = dim V - dim K = dim X - dim (ker L) = dim W`.
  have hfin : finrank ℝ Kᗮ = finrank ℝ W := by
    have e1 := Submodule.finrank_add_finrank_orthogonal K
    have e2 := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker L)
    rw [← hW] at e2
    have e3 := (LinearEquiv.ofBijective B hB).finrank_eq
    have e4 := (Submodule.equivMapOfInjective B hB.1 K).finrank_eq
    rw [← hker] at e4
    omega
  -- Multiplicativity of `normDet` for a composition through an equal-dimensional space.
  rw [hcomp]
  exact LinearMap.normDet_comp_of_finrank_eq _ _ hfin

/-- **Chain rule for the co-area factor** (Simon Ch. 3, (2.7)–(2.8), `chapter-03.txt`
lines 412–428, where `J^{M*}_f` is reduced to the `C¹` case along charts): let `A : ℝⁿ → ℝᴺ` be
injective with range `T`, `L : T → ℝᵐ` linear and `Γ = L ∘ A`. Then
`normDet L* · normDet A = normDet (A ∘ ι_{ker Γ}) · normDet Γ*`.
The corestriction `A' : ℝⁿ → T` of `A` is bijective with the same `normDet`, `Γ = L ∘ A'` and
`range L = range Γ`. If `Γ` is not surjective, both adjoints have `normDet` zero
(`Submission.coarea_normDet_adjoint_eq_horizontal`). Otherwise `normDet P* = normDet (P ∘ ι)` for
the inclusion `ι` of `(ker P)ᗮ`, `P = L, Γ`; `ker L = A'(K)` for `K = ker Γ`, and with
`W = (ker L)ᗮ`, `g = p_W ∘ A' ∘ ι_{Kᗮ}`:
`normDet A' = normDet (A' ∘ ι_K) · normDet g` (`Submission.coarea_normDet_block_triangular`) and
`normDet (Γ ∘ ι_{Kᗮ}) = normDet (L ∘ ι_W) · normDet g`
(`Submission.coarea_normDet_horizontal_comp`). -/
theorem Submission.coarea_normDet_chain_rule : ∀ (n N m : ℕ) (T : Submodule ℝ (Rn N))
    (A : Rn n →ₗ[ℝ] Rn N) (L : T →ₗ[ℝ] Rn m) (Γ : Rn n →ₗ[ℝ] Rn m), Function.Injective A →
    LinearMap.range A = T → (∀ (v : Rn n) (hv : A v ∈ T), Γ v = L ⟨A v, hv⟩) →
    (LinearMap.adjoint L).normDet * A.normDet =
      (A ∘ₗ (LinearMap.ker Γ).subtype).normDet * (LinearMap.adjoint Γ).normDet := by
  intro n N m T A L Γ hA hT hΓ
  -- Step 1(i): `A` corestricts to a bijection `A' : ℝⁿ → T` with `Γ = L ∘ A'`; corestricting
  -- does not change `normDet`.
  have hmem : ∀ v, A v ∈ T := fun v ↦ hT ▸ LinearMap.mem_range_self A v
  obtain ⟨A', hA'⟩ : ∃ A' : Rn n →ₗ[ℝ] T, A' = A.codRestrict T hmem := ⟨_, rfl⟩
  have hA'v : ∀ v, (A' v : Rn N) = A v := fun v ↦ by rw [hA']; rfl
  have hbij : Function.Bijective A' := by
    refine ⟨fun v w h ↦ hA (by rw [← hA'v, ← hA'v, h]), ?_⟩
    rintro ⟨t, ht⟩
    obtain ⟨v, rfl⟩ : t ∈ LinearMap.range A := hT ▸ ht
    exact ⟨v, Subtype.ext (hA'v v)⟩
  have hΓA' : ∀ v, Γ v = L (A' v) := fun v ↦ by
    rw [hΓ v (hmem v)]
    exact congrArg L (Subtype.ext (hA'v v).symm)
  have hnA : A.normDet = A'.normDet := by
    rw [hA', LinearMap.normDet_codRestrict]
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℝ (Rn n), K = LinearMap.ker Γ := ⟨_, rfl⟩
  rw [← hK]
  have hnAK : (A ∘ₗ K.subtype).normDet = (A' ∘ₗ K.subtype).normDet := by
    have hKT : ∀ k : K, (A ∘ₗ K.subtype) k ∈ T := fun k ↦ hmem k
    have h : A' ∘ₗ K.subtype = (A ∘ₗ K.subtype).codRestrict T hKT :=
      LinearMap.ext fun k ↦ Subtype.ext (hA'v k)
    rw [h, LinearMap.normDet_codRestrict]
  -- Step 2: `range L = range Γ`, since `A'` is onto `T`; so `L` is onto iff `Γ` is.
  by_cases hsurj : Function.Surjective Γ
  · -- Step 4: `normDet P* = normDet (P ∘ ι_{(ker P)ᗮ})` for `P = L, Γ`, and `ker L = A'(K)`.
    have hLsurj : Function.Surjective L := fun y ↦ by
      obtain ⟨v, hv⟩ := hsurj y
      exact ⟨A' v, (hΓA' v).symm.trans hv⟩
    rw [(Submission.coarea_normDet_adjoint_eq_horizontal L).1 hLsurj,
      (Submission.coarea_normDet_adjoint_eq_horizontal Γ).1 hsurj, ← hK]
    have hker : LinearMap.ker L = K.map A' := by
      rw [hK, show Γ = L ∘ₗ A' from LinearMap.ext hΓA', LinearMap.ker_comp,
        Submodule.map_comap_eq_of_surjective hbij.2]
    obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ T, W = (LinearMap.ker L)ᗮ := ⟨_, rfl⟩
    rw [← hW]
    -- Step 5: `A'` is block triangular along `K ⊕ Kᗮ → A'(K) ⊕ W`.
    have hblock := Submission.coarea_normDet_block_triangular A' K W hbij (by rw [hW, hker])
    -- Step 6: `Γ ∘ ι_{Kᗮ} = (L ∘ ι_W) ∘ (p_W ∘ A' ∘ ι_{Kᗮ})`.
    have hstep := Submission.coarea_normDet_horizontal_comp A' L Γ K W hbij hΓA' hK hW
    -- Step 7.
    rw [hnA, hblock, hnAK, hstep]
    ring
  · -- Step 3: neither `L` nor `Γ` is onto, so both adjoints have `normDet` zero.
    have hLsurj : ¬ Function.Surjective L := fun hL ↦ hsurj fun y ↦ by
      obtain ⟨t, ht⟩ := hL y
      obtain ⟨v, rfl⟩ := hbij.2 t
      exact ⟨v, (hΓA' v).trans ht⟩
    rw [(Submission.coarea_normDet_adjoint_eq_horizontal L).2 hLsurj,
      (Submission.coarea_normDet_adjoint_eq_horizontal Γ).2 hsurj, zero_mul, mul_zero]

/-- **Simon Ch. 3, 2.1–2.2 and (2.7)** (`chapter-03.txt` lines 335–360 and 412–418), along a
chart: let `A : ℝⁿ → ℝᴺ` be injective with `range A` a weighted approximate tangent plane of `M`
at `x`, `θ x ≠ 0`, and let `f` have line derivative `Γ w` at `x` in every direction `A w`. Then
`T_x M = range A` (uniqueness of weighted tangent planes, SimonGMT
`HasWeightedApproximateTangentSpaceAt.unique`), `L = Γ ∘ A⁻¹` is a tangential differential on
`range A`, it is `d^M f_x` (uniqueness of line derivatives, `HasLineDerivAt.unique`), and
`J^{M*}_f(x) · normDet A = normDet (A ∘ ι_{ker Γ}) · normDet Γ*` by the chain rule
`Submission.coarea_normDet_chain_rule` applied to `T = range A`, `A`, `L` and `Γ`. -/
theorem Submission.chart_coarea_jacobian_identification : ∀ (n N m : ℕ) (M : Set (Rn N))
    (θ : Rn N → ℝ) (f : Rn N → Rn m) (x : Rn N) (A : Rn n →L[ℝ] Rn N) (Γ : Rn n →L[ℝ] Rn m),
    θ x ≠ 0 → Function.Injective A →
    HasWeightedApproximateTangentSpaceAt n M θ x (LinearMap.range A.toLinearMap) →
    (∀ w : Rn n, HasLineDerivAt ℝ f (Γ w) x (A w)) →
    approxTangentPlane n M θ x = LinearMap.range A.toLinearMap ∧
    (∃ L : ↥(LinearMap.range A.toLinearMap) →L[ℝ] Rn m,
      HasTangentialDifferentialAt (LinearMap.range A.toLinearMap) f x L) ∧
    coareaJacobian (approxTangentPlane n M θ x) f x * A.toLinearMap.normDet =
      (A.toLinearMap ∘ₗ (LinearMap.ker Γ.toLinearMap).subtype).normDet *
        (LinearMap.adjoint Γ.toLinearMap).normDet := by
  intro n N m M θ f x A Γ hθ hA hT hΓ
  set T : Submodule ℝ (Rn N) := LinearMap.range A.toLinearMap
  -- (i) `T_x M = T`: the chosen plane and `T` are both weighted tangent planes and `θ x ≠ 0`.
  have hplane : approxTangentPlane n M θ x = T := by
    have h : ∃ P : Submodule ℝ (Rn N), HasWeightedApproximateTangentSpaceAt n M θ x P := ⟨T, hT⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique hθ
      h.choose_spec hT
  -- (ii) `L = Γ ∘ e⁻¹`, `e : ℝⁿ ≃ T` induced by `A`, has line derivative `Γ w` along `e w = A w`.
  let e : Rn n ≃ₗ[ℝ] T := LinearEquiv.ofInjective A.toLinearMap hA
  have he : ∀ w : Rn n, (e w : Rn N) = A w := fun _ ↦ rfl
  obtain ⟨L, hLe⟩ : ∃ L : T →L[ℝ] Rn m, ∀ w : Rn n, L (e w) = Γ w :=
    ⟨LinearMap.toContinuousLinearMap (Γ.toLinearMap ∘ₗ e.symm.toLinearMap), fun w ↦ by simp⟩
  have hL : HasTangentialDifferentialAt T f x L := by
    intro τ
    obtain ⟨w, rfl⟩ := e.surjective τ
    rw [hLe, he]
    exact hΓ w
  -- `d^M f_x = L`: both are line derivatives of `f` at `x` in every direction `τ ∈ T`.
  have hdiff : tangentialDifferential T f x = L := by
    have h : ∃ L' : T →L[ℝ] Rn m, HasTangentialDifferentialAt T f x L' := ⟨L, hL⟩
    rw [tangentialDifferential, dite_eq_left h]
    exact ContinuousLinearMap.ext fun τ ↦ (h.choose_spec τ).unique (hL τ)
  -- (iii) `J^{M*}_f(x) = normDet L*`, and `Γ v = L (A v)` feeds the co-area chain rule.
  refine ⟨hplane, ⟨L, hL⟩, ?_⟩
  rw [hplane, coareaJacobian, hdiff]
  refine Submission.coarea_normDet_chain_rule n N m T A.toLinearMap L.toLinearMap Γ.toLinearMap
    hA rfl fun v hv ↦ ?_
  show Γ v = L ⟨A v, hv⟩
  rw [show (⟨A v, hv⟩ : T) = e v from Subtype.ext (he v).symm, hLe]
/-- Parent 0.1 of the co-area formula on a chart piece, the case `m = 0`: `ℝ⁰` is a point,
`L⁰` is the unit point mass, `J^{M*}_f ≡ 1` (the adjoint `ℝ⁰ → T_x M` has zero-dimensional
domain) and every slice `B ∩ f⁻¹(y)` is `B`, so both sides equal `∫_B φ dHᵏ`. -/
theorem Submission.chartPC_coarea_dim_zero {k ℓ : ℕ} (M : Set (Rn (0 + k + ℓ)))
    (θ : Rn (0 + k + ℓ) → ℝ) (f : Rn (0 + k + ℓ) → Rn 0) (B : Set (Rn (0 + k + ℓ)))
    (φ : Rn (0 + k + ℓ) → ℝ≥0∞) :
    AEMeasurable (fun y : Rn 0 ↦ ∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) volume ∧
      ∫⁻ x in B, φ x * ENNReal.ofReal (coareaJacobian (approxTangentPlane (0 + k) M θ x) f x)
          ∂μHE[0 + k] =
        ∫⁻ y, (∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) ∂volume := by
  refine ⟨Subsingleton.measurable.aemeasurable, ?_⟩
  have hslice : ∀ y : Rn 0, B ∩ f ⁻¹' {y} = B := fun y ↦
    inter_eq_left.2 fun x _ ↦ Subsingleton.elim (f x) y
  have hJ : ∀ x, coareaJacobian (approxTangentPlane (0 + k) M θ x) f x = 1 := fun x ↦
    LinearMap.normDet_of_subsingleton _
  have hμ : (μHE[0 + k] : Measure (Rn (0 + k + ℓ))) = μHE[k] :=
    congrArg (fun d ↦ (μHE[d] : Measure (Rn (0 + k + ℓ)))) (Nat.zero_add k)
  simp only [hslice, hJ, hμ, ENNReal.ofReal_one, mul_one, lintegral_const,
    volume_euclideanSpace_eq_dirac, measure_univ]

/-- **Simon Ch. 3, co-area formula (2.9) on one `C¹` chart piece** (`chapter-03.txt` lines
412–428: (2.8) "follows from the `C¹` case … in a similar manner to the procedure used for the
discussion of the area formula", lines 377–389). Assume the chart lemma (CT), the frozen
statement of `Submission.chart_approx_tangent_and_differential`. Let `n = m + k` with `k > 0`,
`ψ : D → ℝ^{n+ℓ}` a `C¹` chart with injective `Dψ`, injective on the open set `D ⊆ ℝⁿ`, and
`G : ℝⁿ → ℝᵐ` a `C¹` map with `f ∘ ψ = G` and `D(f ∘ ψ) = DG` on the Borel set `E ⊆ D`. Then
for Borel `B ⊆ ψ(E) ∩ M` and Borel `φ ≥ 0`, `y ↦ ∫_{B ∩ f⁻¹(y)} φ dHᵏ` is `Lᵐ`-a.e.
measurable and `∫_B φ J^{M*}_f dHⁿ = ∫_{ℝᵐ} ∫_{B ∩ f⁻¹(y)} φ dHᵏ dLᵐ(y)`.

Proof: for `m = 0` see `chartPC_coarea_dim_zero`. Otherwise pull `B` back to the Borel set
`B' = E ∩ ψ⁻¹(B)`; then `ψ(B') = B` and `B ∩ f⁻¹(y) = ψ(B' ∩ G⁻¹(y))`, so the right side is
the `C¹` parametric co-area formula `Submission.c1_parametric_coarea_formula` on `B'`. The left
side is `∫_{B'} φ(ψ u) J^{M*}_f(ψ u) Jψ(u) du` by the injective area formula for `ψ` (SimonGMT
`weighted_area_formula_volume_of_injective_derivative`, arbitrary non-negative integrand), and
(CT) with `Submission.chart_coarea_jacobian_identification` gives
`J^{M*}_f(ψ u) Jψ(u) = normDet(Dψ(u) ∘ ι_{ker DG(u)}) normDet(DG(u)*)`, the `C¹` integrand, for
`Lⁿ`-a.e. `u ∈ B'` (`Jψ = normDet Dψ`; `D(f ∘ ψ)(u) = DG(u)` on `E`). -/
theorem Submission.chart_piece_coarea_formula : (∀ (n ℓ p : ℕ) (M U : Set (Rn (n + ℓ)))
    (θ : Rn (n + ℓ) → ℝ) (f : Rn (n + ℓ) → Rn p) (V : Set (Rn n)) (ψ : Rn n → Rn (n + ℓ)),
    NullMeasurableSet M μHE[n] → IsPositiveLocallyIntegrableWeight n M θ → IsOpen U → M ⊆ U →
    LocallyLipschitzOn U f → IsOpen V → ContDiffOn ℝ 1 ψ V →
    (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) →
    ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ V → ψ u ∈ M →
      HasWeightedApproximateTangentSpaceAt n M θ (ψ u)
          (LinearMap.range (fderiv ℝ ψ u).toLinearMap) ∧
        DifferentiableAt ℝ (f ∘ ψ) u ∧
        ∀ w : Rn n, HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w)) →
    ∀ (m k ℓ : ℕ) (M U : Set (Rn (m + k + ℓ))) (θ : Rn (m + k + ℓ) → ℝ)
      (f : Rn (m + k + ℓ) → Rn m) (D E : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn (m + k + ℓ))
      (G : Rn (m + k) → Rn m),
      0 < k → NullMeasurableSet M μHE[m + k] → IsPositiveLocallyIntegrableWeight (m + k) M θ →
      IsOpen U → M ⊆ U → LocallyLipschitzOn U f → IsOpen D → ContDiffOn ℝ 1 ψ D → InjOn ψ D →
      (∃ K, LipschitzOnWith K ψ D) → (∀ u ∈ D, Function.Injective (fderiv ℝ ψ u)) →
      ContDiff ℝ 1 G → MeasurableSet E → E ⊆ D →
      (∀ u ∈ E, f (ψ u) = G u ∧ HasFDerivAt (f ∘ ψ) (fderiv ℝ G u) u) →
      ∀ B ⊆ ψ '' E ∩ M, MeasurableSet B → ∀ φ : Rn (m + k + ℓ) → ℝ≥0∞, Measurable φ →
        AEMeasurable (fun y : Rn m ↦ ∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) volume ∧
          ∫⁻ x in B, φ x * ENNReal.ofReal (coareaJacobian (approxTangentPlane (m + k) M θ x) f x)
              ∂μHE[m + k] =
            ∫⁻ y, (∫⁻ x in B ∩ f ⁻¹' {y}, φ x ∂μHE[k]) ∂volume := by
  intro hCT m k ℓ M U θ f D E ψ G hk hM hθ hU hMU hf hD hψ hψinj _ hψD hG hE hED hEG
    B hB hBm φ hφ
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Submission.chartPC_coarea_dim_zero M θ f B φ
  -- The Borel parameter set `B' = E ∩ ψ⁻¹(B)`, with `ψ(B') = B`.
  set B' : Set (Rn (m + k)) := E ∩ ψ ⁻¹' B with hB'
  have hB'D : B' ⊆ D := inter_subset_left.trans hED
  have hB'm : MeasurableSet B' := by
    have h := hE.subtype_image (((hψ.continuousOn.mono hED).domRestrict.measurable) hBm)
    rwa [domRestrict_eq, preimage_comp, Subtype.image_preimage_coe] at h
  have himage : ψ '' B' = B := by
    rw [hB', image_inter_preimage]
    exact inter_eq_right.2 fun x hx ↦ (hB hx).1
  -- Slices: `B ∩ f⁻¹(y) = ψ(B' ∩ G⁻¹(y))`, since `f ∘ ψ = G` on `E`.
  have hslice : ∀ y, ψ '' (B' ∩ G ⁻¹' {y}) = B ∩ f ⁻¹' {y} := by
    intro y
    ext x
    constructor
    · rintro ⟨u, ⟨⟨huE, hux⟩, huy⟩, rfl⟩
      refine ⟨hux, ?_⟩
      rw [mem_preimage, (hEG u huE).1]
      exact huy
    · rintro ⟨hxB, hxy⟩
      obtain ⟨u, huE, rfl⟩ := (hB hxB).1
      refine ⟨u, ⟨⟨huE, hxB⟩, ?_⟩, rfl⟩
      rw [mem_preimage, ← (hEG u huE).1]
      exact hxy
  -- Right side: the `C¹` parametric co-area formula on `B'`.
  obtain ⟨hmeas, hc1⟩ := Submission.c1_parametric_coarea_formula m k (m + k + ℓ) D ψ G hm hk hD
    hψ hψinj hG B' hB'D hB'm φ hφ
  simp only [hslice] at hmeas hc1
  refine ⟨hmeas, ?_⟩
  rw [← hc1]
  -- Left side: the injective area formula for `ψ` on `B'`, with an arbitrary integrand.
  have harea := Poincare.SimonGMT.Chapter02.weighted_area_formula_volume_of_injective_derivative
    hB'm (fun u hu ↦ (hψ.contDiffAt (hD.mem_nhds (hB'D hu))).differentiableAt one_ne_zero)
    (fun u hu ↦ hψD u (hB'D hu)) (hψinj.mono hB'D)
    fun x ↦ φ x * ENNReal.ofReal (coareaJacobian (approxTangentPlane (m + k) M θ x) f x)
  rw [himage, finrank_euclideanSpace_fin] at harea
  rw [harea]
  -- Pointwise for a.e. `u ∈ B'`: `J^{M*}_f(ψ u) Jψ(u)` is the integrand of the `C¹` formula.
  refine setLIntegral_congr_fun_ae hB'm ?_
  filter_upwards [hCT (m + k) ℓ m M U θ f D ψ hM hθ hU hMU hf hD hψ hψD] with u hu huB'
  have huM : ψ u ∈ M := (hB huB'.2).2
  obtain ⟨htan, -, hline⟩ := hu (hB'D huB') huM
  rw [(hEG u huB'.1).2.fderiv] at hline
  have hJ := (Submission.chart_coarea_jacobian_identification (m + k) (m + k + ℓ) m M θ f (ψ u)
    (fderiv ℝ ψ u) (fderiv ℝ G u) (hθ.1 _ huM).ne' (hψD u (hB'D huB')) htan hline).2.2
  have hJ0 : 0 ≤ coareaJacobian (approxTangentPlane (m + k) M θ (ψ u)) f (ψ u) :=
    LinearMap.normDet_nonneg _
  rw [← hJ, ENNReal.ofReal_mul hJ0, Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet]
  ring

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
