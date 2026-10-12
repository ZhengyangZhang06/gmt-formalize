<!-- theorem-id: gmt-ch03/root.chart_tangent_differential-a1.chart_blowup_tangent-a1.chart_area_integral-a1 -->

## Theorem `Submission.chartTD_injective_area_setIntegral`

Let n, N ∈ ℕ, B ⊆ ℝⁿ open, ψ : ℝⁿ → ℝᴺ K-Lipschitz on B (K ∈ ℝ≥0) and injective on B, and g : ℝᴺ → ℝ continuous. Then ∫_{ψ(B)} g dHⁿ = ∫_B g(ψ(v))·Jψ(v) dLⁿ(v), where Jψ(v) := normDet(Dψ(v)) with Dψ(v) = fderiv ℝ ψ v, Hⁿ = μHE[n] and Lⁿ = volume; both sides are Bochner integrals (no integrability assumption).

Node: `root.chart_tangent_differential-a1.chart_blowup_tangent-a1.chart_area_integral-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/99

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.chartTD_injective_area_setIntegral`

```lean
∀ (n N : ℕ) (B : Set (Rn n)) (ψ : Rn n → Rn N) (K : ℝ≥0), IsOpen B → LipschitzOnWith K ψ B → InjOn ψ B → ∀ g : Rn N → ℝ, Continuous g → ∫ y in ψ '' B, g y ∂μHE[n] = ∫ v in B, g (ψ v) * (fderiv ℝ ψ v).toLinearMap.normDet
```

### Frozen project context

`GMT/Ch03/Contract.lean` at `d09bc8a18ce60face651f042976e8465f21f0f68` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
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

/-- The frozen Chapter 3 contract. -/
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem := by sorry

end GMT.Ch03
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.chart_tangent_differential-a1.chart_blowup_tangent-a1`
- Child DAG node: `root.chart_tangent_differential-a1.chart_blowup_tangent-a1.chart_area_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Selected-node proof step 4 (with step 3(a) for measurability of the Jacobian): Simon Ch. 2, (3.2) and (3.5), the area formula for a one-to-one Lipschitz map on a measurable domain, put in integral form. No sibling child is used. Import note: the SimonGMT area formula on a Lipschitz domain lives in Poincare.SimonGMT.Chapter02.AreaDomain, which GMT.Ch03.Submission does not import; the formalization adds `import Poincare.SimonGMT.Chapter02.AreaDomain` (prebuilt pinned package; the frozen statement elaborates identically with it).

Notation. Lⁿ := volume on ℝⁿ; Hⁿ := μHE[n] on ℝᴺ; Γ := ψ(B); Dψ(v) := fderiv ℝ ψ v; Jψ(v) := normDet(Dψ(v)).

1. Jacobian. Jψ(v) ≥ 0 for all v (LinearMap.normDet_nonneg). Jψ is Borel measurable on ℝⁿ: v ↦ Dψ(v) is measurable for every map ψ (Mathlib measurable_fderiv), and A ↦ normDet(A) is continuous on ℝⁿ →L ℝᴺ, hence measurable; compose. (Continuity of normDet is SimonGMT Chapter02.continuous_normDet, visible after the AreaDomain import. Its proof: normDet(A) ≥ 0 and normDet(A)² = det(A* ∘L A) (ContinuousLinearMap.normDet_sq), so normDet(A) = √det(A* ∘L A). That is a composition of the continuous maps A ↦ A* (a linear isometric equivalence), A ↦ A* ∘L A (Continuous.clm_comp), det (ContinuousLinearMap.continuous_det) and √.) Put j(v) := Jψ(v).toNNReal ∈ ℝ≥0. Then j is measurable (Measurable.real_toNNReal), (j(v) : ℝ) = Jψ(v) (Real.coe_toNNReal, as Jψ ≥ 0), and (j(v) : [0, ∞]) = ofReal(Jψ(v)) (definition of ENNReal.ofReal).

2. Measurability facts. B is open, hence Borel. ψ is continuous on B (LipschitzOnWith.continuousOn), hence a.e.-measurable for Lⁿ⌞B (ContinuousOn.aemeasurable). Let ν := (Lⁿ⌞B).withDensity(j), i.e. the measure with density v ↦ (j(v) : [0, ∞]) with respect to Lⁿ⌞B. Since ν ≪ Lⁿ⌞B (withDensity_absolutelyContinuous), ψ is also a.e.-measurable for ν (AEMeasurable.mono_ac). Finally Γ = ψ(B) is Borel by the Lusin-Souslin theorem (MeasurableSet.image_of_continuousOn_injOn: B is Borel in the Polish space ℝⁿ and ψ is continuous and injective on B).

3. Reduction of the measure identity. Claim: Hⁿ⌞Γ = ψ_#ν as measures on ℝᴺ. By extensionality (Measure.ext) it suffices to fix a Borel set E ⊆ ℝᴺ and to show Hⁿ(E ∩ Γ) = ν(ψ⁻¹(E)): indeed (Hⁿ⌞Γ)(E) = Hⁿ(E ∩ Γ) (Measure.restrict_apply, E measurable), (ψ_#ν)(E) = ν(ψ⁻¹(E)) (Measure.map_apply_of_aemeasurable), and ν(ψ⁻¹(E)) = ∫⁻_{ψ⁻¹(E)} j d(Lⁿ⌞B) (withDensity_apply', valid for every set because Lⁿ⌞B is s-finite).

4. Weighted area formula. Let w(v) := 1_E(ψ(v)) ∈ {0, 1} ⊆ [0, ∞]; w is a.e.-measurable for Lⁿ⌞B (the measurable indicator of the Borel set E composed with the a.e.-measurable ψ). Apply SimonGMT Chapter02.weighted_area_formula_lipschitzOn_fiberSum (Simon (3.5)) with s = B (open, hence null-measurable), the K-Lipschitz map ψ on B, and the weight w. After rewriting finrank ℝⁿ = n (finrank_euclideanSpace_fin) it reads
   ∫⁻_{ℝᴺ} weightedAreaFiberSum B ψ w y dHⁿ(y) = ∫⁻_B ofReal(areaJacobianWithin ψ B v)·w(v) dLⁿ(v),
where weightedAreaFiberSum B ψ w y is the sum Σ' of w(v) over the fibre {v : v ∈ B ∧ ψ(v) = y} (SimonGMT areaFiber), and areaJacobianWithin ψ B v = normDet(fderivWithin ℝ ψ B v).

5. Left side. Fix y ∈ ℝᴺ. If y ∉ Γ, the fibre is empty and the sum is 0 = 1_{E∩Γ}(y) (tsum_empty). If y = ψ(v₀) with v₀ ∈ B, then any two fibre elements a, b satisfy ψ(a) = y = ψ(b) with a, b ∈ B, so a = b by injectivity of ψ on B; the fibre is therefore a subsingleton containing v₀ and the sum equals w(v₀) = 1_E(ψ(v₀)) = 1_E(y) = 1_{E∩Γ}(y) (tsum_eq_single). Hence the integrand on the left is the indicator 1_{E∩Γ}, and since E ∩ Γ is Borel (step 2) the left side equals Hⁿ(E ∩ Γ) (lintegral_indicator_one).

6. Right side. For v ∈ B, openness of B gives fderivWithin ℝ ψ B v = fderiv ℝ ψ v (fderivWithin_of_isOpen), so areaJacobianWithin ψ B v = Jψ(v) and ofReal(areaJacobianWithin ψ B v)·w(v) = ofReal(Jψ(v))·1_E(ψ(v)) = 1_{ψ⁻¹(E)}(v)·j(v) (check the cases ψ(v) ∈ E and ψ(v) ∉ E). Hence (setLIntegral_congr_fun on the Borel set B) the right side equals ∫⁻ 1_{ψ⁻¹(E)}·j d(Lⁿ⌞B) = ∫⁻_{ψ⁻¹(E)} j d(Lⁿ⌞B) (lintegral_indicator₀; ψ⁻¹(E) is null-measurable for Lⁿ⌞B because ψ is a.e.-measurable there, AEMeasurable.nullMeasurable), which is ν(ψ⁻¹(E)) by step 3.

7. Steps 4-6 give Hⁿ(E ∩ Γ) = ν(ψ⁻¹(E)) for every Borel set E ⊆ ℝᴺ, so by step 3, Hⁿ⌞Γ = ψ_#ν.

8. Integral identity. By step 7,
   ∫_Γ g dHⁿ = ∫ g d(ψ_#ν) = ∫ g(ψ(v)) dν(v) = ∫ j(v)•g(ψ(v)) d(Lⁿ⌞B)(v) = ∫_B g(ψ(v))·Jψ(v) dv.
The second equality is the change of variables for push-forward measures (integral_map: ψ is a.e.-measurable for ν, and g is continuous, hence a.e.-strongly measurable for ψ_#ν); the third is integration against a density (integral_withDensity_eq_integral_smul, j measurable); the fourth uses NNReal.smul_def and (j(v) : ℝ) = Jψ(v). Each of these is an identity of Bochner integrals valid without any integrability assumption (integrability is transported along the same identities, and both sides are 0 in the non-integrable case), so continuity of g is the only hypothesis needed. ∎

Formalization aid (optional; the numbered proof above is complete on its own). The following Lean script for exactly this frozen statement was compiled by the parent decomposition session against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in the contract scope shown; `#print axioms` reported only propext, Classical.choice, Quot.sound.

```lean
import GMT.Ch03.Submission
import Poincare.SimonGMT.Chapter02.AreaDomain
open Filter MeasureTheory Module Set
open scoped CompactlySupported ENNReal NNReal Topology
namespace GMT.Ch03
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt HasWeightedApproximateTangentSpaceAt PurelyUnrectifiable blowUpMap)

theorem Submission.chartTD_injective_area_setIntegral : (∀ (n N : ℕ) (B : Set (Rn n)) (ψ : Rn n → Rn N) (K : ℝ≥0), IsOpen B → LipschitzOnWith K ψ B → InjOn ψ B → ∀ g : Rn N → ℝ, Continuous g → ∫ y in ψ '' B, g y ∂μHE[n] = ∫ v in B, g (ψ v) * (fderiv ℝ ψ v).toLinearMap.normDet) := by
  intro n N B ψ K hB hLip hinj g hg
  set J : Rn n → ℝ := fun v => (fderiv ℝ ψ v).toLinearMap.normDet with hJdef
  have hJmeas : Measurable J :=
    Poincare.SimonGMT.Chapter02.continuous_normDet.measurable.comp (measurable_fderiv ℝ ψ)
  set j : Rn n → ℝ≥0 := fun v => (J v).toNNReal with hjdef
  have hjmeas : Measurable j := hJmeas.real_toNNReal
  set ν : Measure (Rn n) := (volume.restrict B).withDensity (fun v => (j v : ℝ≥0∞)) with hνdef
  have hψcont : ContinuousOn ψ B := hLip.continuousOn
  have hBmeas : MeasurableSet B := hB.measurableSet
  have hψae : AEMeasurable ψ (volume.restrict B) := hψcont.aemeasurable hBmeas
  have hψν : AEMeasurable ψ ν := hψae.mono_ac (withDensity_absolutelyContinuous _ _)
  have hΓ : MeasurableSet (ψ '' B) := hBmeas.image_of_continuousOn_injOn hψcont hinj
  have hmeas : (μHE[n] : Measure (Rn N)).restrict (ψ '' B) = Measure.map ψ ν := by
    ext E hE
    rw [Measure.restrict_apply hE, Measure.map_apply_of_aemeasurable hψν hE, hνdef,
      withDensity_apply' _ _]
    have hw : AEMeasurable (fun v => E.indicator (1 : Rn N → ℝ≥0∞) (ψ v)) (volume.restrict B) :=
      (measurable_one.indicator hE).comp_aemeasurable hψae
    have harea := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitzOn_fiberSum
      hB.nullMeasurableSet hLip hw
    rw [finrank_euclideanSpace_fin] at harea
    -- left side: fibre sum is the indicator of E ∩ ψ '' B
    have hfib : ∀ y, Poincare.SimonGMT.Chapter02.weightedAreaFiberSum B ψ
        (fun v => E.indicator (1 : Rn N → ℝ≥0∞) (ψ v)) y = (E ∩ ψ '' B).indicator 1 y := by
      intro y
      by_cases hy : y ∈ ψ '' B
      · obtain ⟨v, hv, rfl⟩ := hy
        have hsub : Subsingleton (Poincare.SimonGMT.Chapter02.areaFiber B ψ (ψ v)) := by
          constructor
          rintro ⟨a, ha, hav⟩ ⟨b, hb, hbv⟩
          exact Subtype.ext (hinj ha hb (hav.trans hbv.symm))
        let p : Poincare.SimonGMT.Chapter02.areaFiber B ψ (ψ v) := ⟨v, hv, rfl⟩
        unfold Poincare.SimonGMT.Chapter02.weightedAreaFiberSum
        rw [tsum_eq_single p (fun b hb => absurd (Subsingleton.elim b p) hb)]
        show E.indicator (1 : Rn N → ℝ≥0∞) (ψ v) = _
        by_cases hE' : ψ v ∈ E
        · rw [Set.indicator_of_mem hE',
            Set.indicator_of_mem (show ψ v ∈ E ∩ ψ '' B from ⟨hE', v, hv, rfl⟩)]
        · rw [Set.indicator_of_notMem hE', Set.indicator_of_notMem (fun h => hE' h.1)]
      · have hemp : IsEmpty (Poincare.SimonGMT.Chapter02.areaFiber B ψ y) :=
          ⟨fun x => hy ⟨x.1, x.2.1, x.2.2⟩⟩
        unfold Poincare.SimonGMT.Chapter02.weightedAreaFiberSum
        rw [tsum_empty, Set.indicator_of_notMem]
        exact fun h => hy h.2
    simp_rw [hfib] at harea
    rw [lintegral_indicator_one (hE.inter hΓ)] at harea
    rw [harea, ← lintegral_indicator₀ (hψae.nullMeasurable hE)]
    refine setLIntegral_congr_fun hBmeas (fun x hx => ?_)
    simp only [Poincare.SimonGMT.Chapter02.areaJacobianWithin, fderivWithin_of_isOpen hB hx]
    by_cases hxE : ψ x ∈ E
    · rw [Set.indicator_of_mem hxE, Set.indicator_of_mem (show x ∈ ψ ⁻¹' E from hxE)]
      simp [hjdef, hJdef, ENNReal.ofReal]
    · rw [Set.indicator_of_notMem hxE, Set.indicator_of_notMem (show x ∉ ψ ⁻¹' E from hxE)]
      simp
  rw [hmeas, integral_map hψν hg.aestronglyMeasurable, hνdef,
    integral_withDensity_eq_integral_smul hjmeas]
  congr 1
  funext v
  rw [NNReal.smul_def, smul_eq_mul, hjdef]
  simp only
  rw [Real.coe_toNNReal _ (LinearMap.normDet_nonneg _), mul_comm]

end GMT.Ch03
```

## Key steps

1. Jψ = normDet ∘ Dψ is Borel (measurable_fderiv + continuity of normDet, SimonGMT continuous_normDet) and ≥ 0; ψ is continuous on B and ψ(B) is Borel (Lusin-Souslin).
2. Reduce Hⁿ⌞ψ(B) = ψ_#((Lⁿ⌞B).withDensity Jψ) to Hⁿ(E ∩ ψ(B)) = ∫⁻_{B ∩ ψ⁻¹E} Jψ for Borel E.
3. Apply SimonGMT weighted_area_formula_lipschitzOn_fiberSum with weight 1_E∘ψ; by injectivity the fibre sum is 1_{E∩ψ(B)}, and on open B the within-Jacobian is Jψ.
4. Transfer to integrals: integral_map then integral_withDensity_eq_integral_smul give ∫_{ψ(B)} g dHⁿ = ∫_B g(ψ(v))Jψ(v) dv.

## Reference use

### local-project

Queries:
- `cat local-references/d498d77b74ea2063/manifest.json (project d09bc8a, Mathlib 25730c7c)`
- `rg -n "blowUpMap|HasApproximateTangentSpaceAt" project/GMT/Ch03/Contract.lean`
- `rg -n "chartTD_|approx_tangent" project/GMT (no match)`
- `rg -n "theorem normDet_nonneg|theorem _root_.ContinuousLinearMap.normDet_sq|theorem euclideanHausdorffMeasure_image_eq_normDet_mul_volume|theorem normDet_eq_prod_singularValues|theorem normDet_of_subsingleton" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n "continuous_normDet|normDet_le|normDet.*opNorm" mathlib/Mathlib (no continuity lemma or operator-norm bound for normDet in Mathlib; only normDet_smul)`
- `rg -n "setIntegral.*image.*normDet|integral_image_eq_integral_abs_det_fderiv_smul" mathlib/Mathlib (only the equidimensional |det| change of variables in MeasureTheory/Function/Jacobian.lean)`
- `rg -n "theorem norm_fderiv_le_of_lipschitzOn|theorem HasFDerivAt.lim" mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `rg -n "theorem measurable_fderiv" mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `rg -n "theorem ContinuousLinearMap.continuous_det" mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n "euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "theorem MeasurableSet.image_of_continuousOn_injOn" mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `rg -n "theorem integral_withDensity_eq_integral_smul|theorem integral_comp_smul|theorem tendsto_integral_filter_of_dominated_convergence" mathlib/Mathlib/MeasureTheory`
- `grep -n "def blowUpMap|def HasApproximateTangentSpaceAt|theorem hasApproximateTangentSpaceAt_submodule" simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (pinned package)`
- `grep -rn "normDet" simongmt/Poincare/SimonGMT | grep theorem (found Chapter02.continuous_normDet in AreaApproximation.lean)`
- `grep -rn "normDet[^\n]*≤|areaJacobianAt[^\n]*≤|≤[^\n]*normDet" simongmt/Poincare/SimonGMT (no operator-norm bound for normDet)`
- `grep -rn "areaJacobianAt" simongmt/Poincare/SimonGMT | grep theorem (found areaJacobianAt_eq_normDet and measurable_areaJacobianAt)`
- `grep -n "theorem" simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean (found integral_area_formula_of_injective_derivative)`
- `grep -rn "theorem.*blowUpMap|theorem.*HasApproximateTangentSpaceAt|Remark 1" simongmt/Poincare/SimonGMT/Chapter03 (no C¹-chart Remark 1.5(2) lemma)`
- `grep -n "theorem weighted_area_formula_lipschitzOn_fiberSum|def weightedAreaFiberSum|def areaFiber|def areaJacobianWithin" simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `grep -n "theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `lake env lean GMT/Scratch/CBTLibVis*.lean (SimonGMT continuous_normDet / integral_area_formula_of_injective_derivative / measurable_areaJacobianAt: not visible after import GMT.Ch03.Submission alone; visible after adding import Poincare.SimonGMT.Chapter02.AreaDomain)`
- `lake env lean GMT/Scratch/CBTComparatorScope4.lean (four frozen statements in the replayed comparator scope)`
- `lake env lean GMT/Scratch/CBTFullCheck4.lean and GMT/Scratch/CBTNoAreaDomain4.lean (all child proofs, the assembly, and #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`

Snapshot manifest: project d09bc8a (Contract.lean byte-identical to the workspace) and Mathlib 25730c7c; SimonGMT is the pinned simongmt package (2b36630). Used from Mathlib: LinearMap.normDet with normDet_nonneg, ContinuousLinearMap.normDet_sq and euclideanHausdorffMeasure_image_eq_normDet_mul_volume; norm_fderiv_le_of_lipschitzOn, HasFDerivAt.lim, measurable_fderiv, ContinuousLinearMap.continuous_det, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, MeasurableSet.image_of_continuousOn_injOn (Lusin-Souslin), integral_withDensity_eq_integral_smul, Measure.integral_comp_smul and tendsto_integral_filter_of_dominated_convergence. Used from SimonGMT: blowUpMap and HasApproximateTangentSpaceAt (Def. 1.4); weighted_area_formula_lipschitzOn_fiberSum and areaJacobianWithin (AreaDomain); weightedAreaFiberSum and areaFiber (AreaMultiplicity, reached through the same import); continuous_normDet (AreaApproximation, reachable through the AreaDomain import); and euclideanHausdorffMeasure_image_le_of_lipschitzOn, which is visible from GMT.Ch03.Submission. Because SimonGMT already proves continuous_normDet, normDet continuity is cited rather than made a child. SimonGMT integral_area_formula_of_injective_derivative (WeightedArea) covers injective maps that are differentiable with injective derivative. The chart_area_integral child keeps the supplied step 4's Lipschitz-domain version, whose hypotheses are incomparable with the library lemma's. No match in Mathlib or SimonGMT for an operator-norm bound on normDet, for the blow-up limit of chart integrals, or for Remark 1.5(2) on C¹ charts; SimonGMT has only the flat-plane case, hasApproximateTangentSpaceAt_submodule. No existing chartTD_* declarations exist in the project. The four statements elaborate in the comparator scope replayed by the verifier's contract_scope, and their proofs compile with standard axioms only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
