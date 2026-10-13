<!-- theorem-id: gmt-ch03/root.de_giorgi-a1 -->

## Theorem `Submission.deGiorgiTheorem_holds`

For n ∈ ℕ, U ⊆ ℝ^{n+1} open and E Lebesgue null-measurable with locally finite perimeter in U: a Gauss-Green pair (μ, ν) for (U, E) exists, and for every Gauss-Green pair (μ, ν), with ∂*E := reducedBoundary U μ ν (points of U where the open-ball averages μ(B_ρ(x))⁻¹∫_{B_ρ(x)}ν dμ converge as ρ ↓ 0 to a unit vector) and ν_E := reducedNormal μ ν (that limit): ∂*E is countably n-rectifiable; μ = Hⁿ⌞∂*E as measures on ℝ^{n+1}; for every x ∈ ∂*E, μ has approximate tangent plane (span{ν_E(x)})^⊥ at x with multiplicity 1 (HasApproxTangentPlaneWithMultiplicity); and for every x ∈ ∂*E and compact K, L^{n+1}(K ∩ (η_{x,r}(E) Δ {y : ⟨y, ν_E(x)⟩ > 0})) → 0 as r ↓ 0.

Node: `root.de_giorgi-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/31, https://github.com/ZhengyangZhang06/gmt-formalize/issues/23, https://github.com/ZhengyangZhang06/gmt-formalize/issues/26

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/372, https://github.com/ZhengyangZhang06/gmt-formalize/issues/373, https://github.com/ZhengyangZhang06/gmt-formalize/issues/375, https://github.com/ZhengyangZhang06/gmt-formalize/issues/377, https://github.com/ZhengyangZhang06/gmt-formalize/issues/380, https://github.com/ZhengyangZhang06/gmt-formalize/issues/382, https://github.com/ZhengyangZhang06/gmt-formalize/issues/386, https://github.com/ZhengyangZhang06/gmt-formalize/issues/388, https://github.com/ZhengyangZhang06/gmt-formalize/issues/390, https://github.com/ZhengyangZhang06/gmt-formalize/issues/393

## Lean problem

Declaration: `Submission.deGiorgiTheorem_holds`

```lean
DeGiorgiTheorem
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

- Parent DAG node: `root`
- Child DAG node: `root.de_giorgi-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 3, (4.2) and Theorem 4.3 with its proof, chapter-03.txt lines 576-746 (printed pp. 81-83). Errata and gaps (stated explicitly): (E1) sign: in the display after (8) (lines 674-686) the printed “0 ≤ ρ_k^{-n}∫ζ_kν_{n+1}dμ_E = ∫_{ρ_k^{-1}E}D_{n+1}ζ” drops the minus sign of (8)/(4.1); correctly ∫_{ρ_k^{-1}E}D_{n+1}ζ = −ρ_k^{-n}∫ζ_kν_{n+1}dμ_E ≤ o(1), so χ_H is non-decreasing (as printed) and (9) and the final display must read {x^{n+1} > λ}, {x^{n+1} > 0} (printed “<”), consistent with (4.1) and (‡‡); (E2) “χ_{ρ_k^{-1}E} → χ_R” (line 655) should read χ_F; (E3) the last step (lines 739-746, “Then by 4.1, (1) and (2) we have μ_{ρ^{-1}E} → Hⁿ⌞{x^{n+1} = 0}”) is terse: it also uses the mass bound (6) to control ∫φ(1 − ν_{n+1})dμ_ρ; written out in Part 4; (E4) “By 1.6 and 3.6 of Ch. 1, the first part of the theorem follows from (‡)” (line 604) is only a sketch: Theorem 1.6 concerns Hⁿ⌞M, not μ_E, so we use the measure form of the 1.6 “⇐” argument (sibling rectifiable_of_tangent_measure) and density comparison (Part 5); (E5) “Repeating the same argument with U ∖ E in place of E” (line 729) uses that (μ, −ν) is a Gauss-Green pair for U ∖ E (Part 1); (E6) for n = 0 the Sobolev inequality is replaced by its one-dimensional L^∞ form.

Notation. N := n + 1; ℝ^N = EuclideanSpace ℝ (Fin N); L^N = volume; Hⁿ = μHE[n]; B_ρ(x) open ball; ω_d = L^d(B_1(0)) (ω₀ = 1); η_{x,r}(y) = r⁻¹(y − x) (blowUpMap); e_N the last basis vector. A Gauss-Green pair (μ, ν) for (U, E) is as in IsGaussGreenPair: μ Borel, μ(ℝ^N ∖ U) = 0, μ(K) < ∞ for compact K ⊆ U, ν μ-measurable, |ν| = 1 μ-a.e., and (GG) ∫_{E∩U} div g = −∫⟨g, ν⟩dμ for C¹ g with compact support in U. By mollification (g_σ → g uniformly, div g_σ → div g a.e. and boundedly, supports in a fixed compact subset of U), (GG) also holds for Lipschitz g with compact support in U. normalAverage(x, ρ) := μ(B_ρ(x))⁻¹∫_{B_ρ(x)} ν dμ (:= 0 if the denominator is 0 or ∞), ∂*E := {x ∈ U : normalAverage(x, ρ) converges as ρ ↓ 0 to a unit vector}, ν_E(x) := the limit (reducedNormal).

Statement. DeGiorgiTheorem: for U ⊆ ℝ^N open and E Lebesgue-null-measurable with HasLocallyFinitePerimeter U E: (0) a Gauss-Green pair exists; and for every Gauss-Green pair (μ, ν): (R) ∂*E is countably n-rectifiable; (M) μ = Hⁿ⌞∂*E; (‡) for every x ∈ ∂*E, HasApproxTangentPlaneWithMultiplicity n μ x P_x 1 with P_x := (span{ν_E(x)})^⊥; (‡‡) for every x ∈ ∂*E and compact K, L^N(K ∩ (η_{x,r}(E) Δ {y : ⟨y, ν_E(x)⟩ > 0})) → 0 as r ↓ 0.

Part 0. (0) is the “⇒” direction of the sibling gauss_green (GaussGreenRepresentation). Fix a pair (μ, ν).

Part 1. Invariances.
1a (complement; erratum E5). (μ, −ν) is a Gauss-Green pair for (U, U ∖ E): ∫_{(U∖E)∩U} div g = ∫_U div g − ∫_{E∩U} div g = 0 + ∫⟨g, ν⟩dμ (∫_{ℝ^N} ∂ᵢgⁱ = 0 for compactly supported C¹ g by Fubini and the fundamental theorem of calculus). Its reduced boundary is ∂*E with normal −ν_E (normalAverage is linear in ν).
1b (scaling, translation, rotation). For x ∈ ℝ^N, r > 0 and an orthogonal R, put E' := R(η_{x,r}(E)), U' := R(η_{x,r}(U)), μ'(B) := r^{-n}μ(η_{x,r}⁻¹(R⁻¹B)) and ν'(y) := Rν(η_{x,r}⁻¹(R⁻¹y)). Then (μ', ν') is a Gauss-Green pair for (U', E') (change of variables y = R η_{x,r}(z): for g' ∈ C¹_c(U'), g := R⁻¹∘g'∘R∘η_{x,r} ∈ C¹_c(U) satisfies div g(z) = r⁻¹(div g')(Rη_{x,r}(z)) and ⟨g(z), ν(z)⟩ = ⟨g'(Rη_{x,r}(z)), Rν(z)⟩ and ∫_{E'∩U'} div g' = r^{-N}·r∫_{E∩U} div g = −r^{-n}∫⟨g, ν⟩dμ = −∫⟨g', ν'⟩dμ'), and normalAverage'(R η_{x,r}(z), ρ) = R normalAverage(z, rρ). Hence z ∈ ∂*E iff Rη_{x,r}(z) ∈ ∂*E' with ν_{E'} = Rν_E. All conclusions (‡), (‡‡) at a point x₀ ∈ ∂*E are equivalent to the corresponding conclusions at 0 for the pair obtained with x = x₀, r = 1 and R with Rν_E(x₀) = e_N. So, in Parts 2-4, 0 ∈ ∂*E and ν_E(0) = e_N.
1c. For x ∈ ∂*E, 0 < μ(B_ρ(x)) for every ρ > 0 (otherwise normalAverage(x, ρ') = 0 for ρ' ≤ ρ and the limit would be 0), and μ(B_ρ(x)) < ∞ for ρ < ρ₀(x) := dist(x, ℝ^N ∖ U) (B̄_ρ(x) ⊆ U compact); here dist(x, ∅) := +∞ (in Lean use infEdist, since Metric.infDist x ∅ = 0).

Part 2. Density estimates at 0 (Simon (1)-(6), lines 607-652). Let ρ₀ := ρ₀(0), V(ρ) := L^N(E ∩ B_ρ(0)), V_c(ρ) := L^N(B_ρ(0) ∖ E) (non-decreasing, hence differentiable a.e.).
(1) ⨍_{B_ρ} ν_N dμ := μ(B_ρ)⁻¹∫_{B_ρ}ν_N dμ → 1 (the N-th component of normalAverage(0, ρ) → (ν_E(0))_N = 1).
(2) ⨍_{B_ρ}|ν − e_N| dμ → 0, in particular ⨍_{B_ρ}|νᵢ| dμ → 0 for i < N: as |ν| = 1 a.e., |ν − e_N|² = 2(1 − ν_N), so ⨍|ν − e_N| ≤ (⨍|ν − e_N|²)^{1/2} = (2(1 − ⨍ν_N))^{1/2} → 0.
(3) For a Lipschitz ζ ≥ 0 with compact support in U, (GG) with g = ζe_N gives ∫ζν_N dμ = −∫_E D_Nζ ≤ ∫_E|Dζ|, and with 1a, ∫ζν_N dμ = ∫_{U∖E} D_Nζ ≤ ∫_{U∖E}|Dζ|.
(4)-(5) Let ρ ∈ (0, ρ₀) be a point where V and V_c are differentiable. For k with 1/k < ρ let ζ_k(y) := φ_k(|y|), φ_k := 1 on [0, ρ − 1/k], 0 on [ρ, ∞), linear in between. Then ζ_k ↑ 1_{B_ρ(0)} pointwise, |Dζ_k| = k on the annulus {ρ − 1/k < |y| < ρ} and 0 a.e. elsewhere, so ∫_E|Dζ_k| = k(V(ρ) − V(ρ − 1/k)) → V'(ρ) and similarly for V_c. By dominated convergence (|ν_N| ≤ 1, μ(B_ρ) < ∞), (3) gives
 (5) ∫_{B_ρ(0)} ν_N dμ ≤ min(V'(ρ), V_c'(ρ)) for a.e. ρ ∈ (0, ρ₀).
(6) By (1) choose ρ₁ ∈ (0, ρ₀) with ∫_{B_ρ}ν_N dμ ≥ μ(B_ρ)/2 for ρ < ρ₁. Since V(ρ) − V(ρ') ≤ L^N(B_ρ ∖ B_{ρ'}), V'(ρ) ≤ Nω_Nρⁿ. Hence μ(B_ρ(0)) ≤ 2V'(ρ), μ(B_ρ(0)) ≤ 2V_c'(ρ) and μ(B_ρ(0)) ≤ 2Nω_Nρⁿ for a.e. ρ ∈ (0, ρ₁); by monotonicity of ρ ↦ μ(B_ρ) (letting a.e. ρ' ↓ ρ) the last bound holds for every ρ ∈ (0, ρ₁): (6') μ(B_ρ(0)) ≤ Cρⁿ, C := 2Nω_N.

Part 3. Blow-ups of E are half-spaces (Simon lines 653-737, with E1, E2). For r > 0 let E_r := η_{0,r}(E), U_r := η_{0,r}(U) (⊇ B_{ρ₀/r}(0)), μ_r(B) := r^{-n}μ(rB), ν^{(r)}(y) := ν(ry); (μ_r, ν^{(r)}) is a Gauss-Green pair for (U_r, E_r) by 1b.
3a. Bounds: for R > 0 and r < ρ₁/R, μ_r(B_R(0)) = r^{-n}μ(B_{rR}(0)) ≤ CRⁿ, and for C¹ g with |g| ≤ 1 and compact support in B_R(0) ⊆ U_r, ∫_{E_r} div g = −∫⟨g, ν^{(r)}⟩dμ_r ≤ μ_r(B_R) ≤ CRⁿ. So the characteristic functions χ_{E_r} are bounded in L¹(B_R) and have uniformly bounded variation |Dχ_{E_r}|(B_R) ≤ CRⁿ (Simon Ch. 2 (2.4)).
3b. Compactness (Simon Ch. 2, Theorem 2.6, chapter-02.txt lines 598-628, proved there by mollification and Arzelà's theorem with reference to [GT01, Thm 7.22]; we write out this route, since BV compactness is not available in SimonGMT/Mathlib). Claim: every sequence r_k ↓ 0 has a subsequence with χ_{E_{r_k}} → u in L¹_loc(ℝ^N); passing to an a.e. convergent subsequence, u ∈ {0, 1} a.e., so u = χ_F for a Lebesgue measurable F (erratum E2). (i) Translation estimate: for R > 0, |h| ≤ 1 and r < ρ₁/(R+1), ∫_{B_R}|χ_{E_r}(y + h) − χ_{E_r}(y)| dy ≤ |h|·μ_r(B_{R+1}) ≤ |h|C(R+1)ⁿ. Indeed, for ψ ∈ C¹_c(B_R) with |ψ| ≤ 1, ∫(χ_{E_r}(y + h) − χ_{E_r}(y))ψ(y) dy = ∫χ_{E_r}(ψ(· − h) − ψ) = −∫₀¹∫_{E_r} div(ψ(· − th)h) dy dt = ∫₀¹∫⟨ψ(y − th)h, ν^{(r)}(y)⟩dμ_r(y) dt ≤ |h|μ_r(B_{R+1}) by (GG) for the scaled pair (the fields ψ(· − th)h are supported in B_{R+1} ⊆ U_r); take the supremum over such ψ (L¹(B_R) norm by duality and density of C¹_c in the unit ball of L^∞). (ii) Hence, with a standard mollifier φ_σ (σ ≤ 1), ‖χ_{E_r} − φ_σ * χ_{E_r}‖_{L¹(B_R)} ≤ ∫φ_σ(h)‖χ_{E_r}(· − h) − χ_{E_r}‖_{L¹(B_R)} dh ≤ σC(R+1)ⁿ. (iii) The functions φ_σ * χ_{E_r} take values in [0, 1] and are Lipschitz with constant σ⁻¹‖Dφ‖_{L¹}, uniformly in r. By Arzelà-Ascoli on B̄_m(0) and a diagonal argument over m ∈ ℕ (σ = 1/m, R = m), some subsequence r_k has φ_{1/m} * χ_{E_{r_k}} converging uniformly on B̄_m(0) for every m. Then, for fixed R and σ = 1/m with m ≥ R, ‖χ_{E_{r_k}} − χ_{E_{r_l}}‖_{L¹(B_R)} ≤ 2σC(R+1)ⁿ + ω_NR^N sup_{B_R}|φ_σ * χ_{E_{r_k}} − φ_σ * χ_{E_{r_l}}|, so (χ_{E_{r_k}}) is Cauchy in L¹(B_R) for every R and converges in L¹_loc.
3c. Horizontal invariance (Simon (7)-(8)). For ζ ∈ C¹_c(ℝ^N), spt ζ ⊆ B_R(0), and i < N: ∫_{E_r} Dᵢζ = −∫ζνᵢ^{(r)}dμ_r and |∫ζνᵢ^{(r)}dμ_r| ≤ sup|ζ| r^{-n}∫_{B_{rR}}|νᵢ|dμ ≤ sup|ζ| CRⁿ ⨍_{B_{rR}}|νᵢ| dμ → 0 by (2), (6'). L¹_loc convergence gives ∫_F Dᵢζ = 0 for all ζ ∈ C¹_c, i < N. Hence χ_F(x', t) is a.e. independent of x' ∈ ℝⁿ: mollifying, u_σ := φ_σ * χ_F is smooth with Dᵢu_σ = 0 (i < N), so u_σ(x', t) = w_σ(t), and u_σ → χ_F in L¹_loc; therefore F = ℝⁿ × H (up to a null set) for a measurable H ⊆ ℝ (for n = 0 there is nothing to prove).
3d. Vertical monotonicity (corrected sign, erratum E1). For ζ ∈ C¹_c(ℝ^N), ζ ≥ 0, spt ζ ⊆ B_R: ∫_{E_r}D_Nζ = −∫ζν_N^{(r)}dμ_r = −∫ζ dμ_r + ∫ζ(1 − ν_N^{(r)})dμ_r ≤ sup ζ · r^{-n}∫_{B_{rR}}(1 − ν_N)dμ ≤ sup ζ · CRⁿ(1 − ⨍_{B_{rR}}ν_N dμ) → 0 by (1), (6') (note 1 − ν_N ≥ 0). So ∫_F D_Nζ ≤ 0. With ζ(x', t) = α(x')β(t), α, β ≥ 0, ∫α = 1: ∫_H β'(t)dt ≤ 0 for all β ∈ C¹_c(ℝ), β ≥ 0, i.e. the distributional derivative of χ_H is a non-negative measure, so χ_H agrees a.e. with a non-decreasing {0, 1}-valued function: H = (λ, ∞) up to a null set, λ ∈ [−∞, ∞], and F = {x : x_N > λ} (erratum: printed (9) has “<”).
3e. λ = 0 (Simon lines 689-733, with E5, E6). Sobolev step: for ζ Lipschitz, ζ ≥ 0, compact support in U, and G ∈ {E, U ∖ E} with the corresponding pair (μ, ±ν):
 (S) ‖ζχ_G‖_{L^{N/(N−1)}} ≤ c_N(∫ζ dμ + ∫_G |Dζ|) if N ≥ 2, and ess sup ζχ_G ≤ ½(∫ζ dμ + ∫_G|Dζ|) if N = 1.
 Proof: for w ∈ C¹_c(ℝ^N), ‖w‖_{N/(N−1)} ≤ c_N‖Dw‖_1 (Gagliardo-Nirenberg-Sobolev inequality, [GT01, Thm 7.10]; Mathlib eLpNorm_le_eLpNorm_fderiv_of_eq; for N = 1, sup|w| ≤ ½∫|w'|, from w(x) = ∫_{−∞}^x w' = −∫_x^∞ w'); it extends to Lipschitz w with compact support by applying it to φ_τ * w and letting τ → 0 (‖D(φ_τ * w)‖₁ ≤ ‖Dw‖₁). Apply it to w_σ := ζ·(φ_σ * χ_G) for small σ: ∫|Dw_σ| ≤ ∫ζ|D(φ_σ * χ_G)| + ∫(φ_σ * χ_G)|Dζ|, and ∫ζ|D(φ_σ * χ_G)| = sup_{|g|≤ζ, g ∈ C¹_c} ∫g·D(φ_σ * χ_G) = sup −∫_G div(φ_σ * g) = sup ±∫⟨φ_σ * g, ν⟩dμ ≤ ∫(φ_σ * ζ)dμ → ∫ζ dμ (|φ_σ * g| ≤ φ_σ * ζ; the easy half of Simon Ch. 2, Lemma 2.5); letting σ ↓ 0 (φ_σ * χ_G → χ_G in L¹_loc and boundedly) gives (S).
 Apply (S) with ζ = ζ_k from (4), k → ∞: for a.e. ρ ∈ (0, ρ₁), with (6), V(ρ)^{(N−1)/N} ≤ c_N(μ(B_ρ) + V'(ρ)) ≤ 3c_N V'(ρ) if N ≥ 2, and 1 ≤ 3V'(ρ)/2 whenever V(ρ) > 0 if N = 1 (ess sup ζ_kχ_E = 1 for large k when V(ρ) > 0). Moreover V(ρ) > 0 for all ρ > 0: otherwise χ_E = 0 a.e. on B_ρ, so ∫ζν_N dμ = −∫_E D_Nζ = 0 for ζ supported in B_ρ, and with ζ_k ↑ 1_{B_{ρ'}} (ρ' < ρ) this gives ∫_{B_{ρ'}}ν_N dμ = 0, contradicting (1) and 1c. For the non-decreasing W := V^{1/N} we get W'(ρ) = V'(ρ)/(N V^{(N−1)/N}) ≥ 1/(3c_N N) (N ≥ 2; for N = 1, W = V and W' ≥ 2/3) at a.e. ρ < ρ₁; since a non-decreasing function satisfies W(ρ) − W(ε) ≥ ∫_ε^ρ W'(t)dt (Lebesgue), letting ε ↓ 0 gives (10) V(ρ) ≥ c'ρ^N for ρ ∈ (0, ρ₁), c' := (3c_N N)^{-N} (resp. 2/3 for N = 1). The same argument for U ∖ E (1a, the second inequality in (5) and (6)) gives (11) V_c(ρ) ≥ c'ρ^N.
 Consequently, for every R > 0 and r < ρ₁/R, L^N(E_r ∩ B_R) = r^{-N}V(rR) ≥ c'R^N and L^N(B_R ∖ E_r) ≥ c'R^N; passing to the L¹_loc limit, L^N(F ∩ B_R) ≥ c'R^N and L^N(B_R ∖ F) ≥ c'R^N for every R > 0. If λ > 0 (or +∞) then F ∩ B_R = ∅ for R < λ; if λ < 0 (or −∞) then B_R ∖ F = ∅ for R < |λ|; both are impossible, so λ = 0 and F = F₀ := {x : x_N > 0}.
3f. (‡‡) (Simon lines 734-739). Every sequence r_k ↓ 0 has a subsequence along which χ_{E_{r_k}} → χ_{F₀} in L¹_loc. Hence χ_{E_r} → χ_{F₀} in L¹_loc as r ↓ 0 (otherwise some compact K, ε > 0 and r_k ↓ 0 would have L^N(K ∩ (E_{r_k} Δ F₀)) ≥ ε for all k, contradicting the subsequence property). Undoing the normalization 1b (x₀ ∈ ∂*E, R with Rν_E(x₀) = e_N; R maps {y : ⟨y, ν_E(x₀)⟩ > 0} onto F₀ and preserves L^N): L^N(K ∩ (η_{x₀,r}(E) Δ {y : ⟨y, ν_E(x₀)⟩ > 0})) → 0 for every compact K. (Only E ∩ U matters: for r < ρ₀(x₀)/R, η_{x₀,r}(E) ∩ B_R = η_{x₀,r}(E ∩ U) ∩ B_R.)

Part 4. (‡) (Simon lines 739-746: “by 4.1, (1) and (2)”, together with (6); erratum E3). Let P := e_N^⊥ = ℝⁿ × {0}. Note that ∫ f dμ_r = r^{-n}∫ f(η_{0,r}(y)) dμ(y), the quantity in HasApproxTangentPlaneWithMultiplicity. Fix f ∈ C_c(ℝ^N) and R > 1 with spt f ⊆ B_{R−1}(0). (i) For φ ∈ C¹_c(B_R(0)) and r < ρ₁/R, (GG) for the scaled pair (μ_r, ν^{(r)}) with g = φe_N gives ∫φν_N^{(r)}dμ_r = −∫_{E_r}D_Nφ → −∫_{F₀}D_Nφ = ∫_P φ dHⁿ as r ↓ 0, by 3f (L¹_loc convergence; D_Nφ is bounded with compact support) and Fubini with the fundamental theorem of calculus in x_N. (ii) Since 1 − ν_N ≥ 0 μ-a.e., |∫φ(1 − ν_N^{(r)})dμ_r| ≤ sup|φ|·r^{-n}∫_{B_{rR}}(1 − ν_N)dμ ≤ sup|φ|·CRⁿ(1 − ⨍_{B_{rR}}ν_N dμ) → 0 by (1) and (6'). With (i): ∫φ dμ_r → ∫_P φ dHⁿ. (iii) For the given f and ε > 0 choose φ ∈ C¹_c(B_R(0)) with sup|f − φ| ≤ ε (mollification). Then |∫f dμ_r − ∫φ dμ_r| ≤ εμ_r(B_R) ≤ εCRⁿ and |∫_P f dHⁿ − ∫_P φ dHⁿ| ≤ εω_nRⁿ, so limsup_{r↓0}|∫f dμ_r − ∫_P f dHⁿ| ≤ ε(C + ω_n)Rⁿ; let ε ↓ 0. Hence HasApproxTangentPlaneWithMultiplicity n μ 0 P 1 (finrank P = n), i.e., after undoing 1b, (‡) holds at every x ∈ ∂*E with P_x = (span{ν_E(x)})^⊥. (For n = 0, P = {0}, H⁰⌞P is the unit mass at 0 and ω₀ = 1; the argument is unchanged.)

Part 5. Rectifiability and μ = Hⁿ⌞∂*E (erratum E4).
5a. μ(ℝ^N ∖ ∂*E) = 0 (Simon line 584, “by virtue of Theorem 3.23 of Ch. 1”). Let W_i := {x ∈ U : |x| < i, dist(x, ℝ^N ∖ U) > 1/i} (open, W̄_i compact ⊆ U; if U = ℝ^N take W_i := B_i(0)); μ⌞W_i is a finite measure and, for x ∈ W_i and small ρ, ball averages for μ⌞W_i and μ at x coincide; it therefore suffices to argue for μ⌞W_i, i ∈ ℕ. ν is bounded, so by the Lebesgue-Besicovitch differentiation theorem for (locally) finite Radon measures on ℝ^N (Simon Ch. 1, Corollary 3.17 with the Symmetric Vitali Property from Besicovitch's covering lemma; Mathlib Besicovitch.vitaliFamily, VitaliFamily.ae_tendsto_average), for μ-a.e. x ∈ U the averages of ν over closed balls B̄_ρ(x) converge to ν(x), and |ν(x)| = 1; the same holds for open balls because B_ρ(x) = ⋃_{ρ'<ρ} B̄_{ρ'}(x) (so the open-ball average is a limit of closed-ball averages with radii < ρ), and μ(B_ρ(x)) ∈ (0, ∞) for small ρ at μ-a.e. x ∈ U (support of μ). Such x belong to ∂*E. As μ(ℝ^N ∖ U) = 0, μ(ℝ^N ∖ ∂*E) = 0.
5b. ∂*E is Borel. For x ∈ U the map ρ ↦ normalAverage(x, ρ) is left-continuous on (0, ρ₀(x)) (μ(B_ρ(x)) and ∫_{B_ρ(x)}ν dμ are continuous from below in ρ), and for fixed ρ, x ↦ μ(B_ρ(x)) is lower semicontinuous and x ↦ ∫_{B_ρ(x)} ν dμ is Borel (Tonelli, with a Borel version of ν). Hence “normalAverage(x, ·) converges as ρ ↓ 0” is equivalent to the Cauchy condition along rational radii, and the limit equals lim_j normalAverage(x, 1/j); so ∂*E = {x ∈ U : Cauchy condition holds and |lim_j normalAverage(x, 1/j)| = 1} is Borel.
5c. (R). With W_i as in 5a, let μ_i := μ⌞W_i (finite). For x ∈ ∂*E ∩ W_i, μ_i has at x the approximate tangent plane P_x with multiplicity 1 (Part 4 and locality: for f ∈ C_c and small r, f∘η_{x,r} is supported in W_i); this holds μ_i-a.e. by 5a. By the sibling rectifiable_of_tangent_measure there is a Borel countably n-rectifiable R_i with μ_i(ℝ^N ∖ R_i) = 0. R := ⋃_i R_i is Borel, countably n-rectifiable, and μ(U ∖ R) = 0. By (‡), Θⁿ(μ, x) = lim_{ρ↓0} μ(B_ρ(x))/(ω_nρⁿ) = 1 for every x ∈ ∂*E (test functions squeezing 1_{B_1(0)} as in Simon Remark 1.5(3), using Hⁿ(P_x ∩ B_1(0)) = ω_n). Simon Ch. 1, Theorem 3.3 (chapter-01.txt lines 602-610; SimonGMT Chapter01.simon_theorem_3_3) with A₁ := A ⊆ ∂*E and A₂ := O open, A ⊆ O ⊆ U, gives Hⁿ(A) ≤ μ(O) (the upper density of μ⌞O at points of O is that of μ). By outer regularity of the locally finite Borel measure μ on the open set U, (D1) Hⁿ(A) ≤ μ(A) for every Borel A ⊆ ∂*E. With A := ∂*E ∖ R: Hⁿ(∂*E ∖ R) ≤ μ(U ∖ R) = 0, so ∂*E ⊆ (∂*E ∖ R) ∪ R is countably n-rectifiable.
5d. (M). Let σ := Hⁿ⌞∂*E (Borel set by 5b). By (D1), σ(K) ≤ μ(K) < ∞ for compact K ⊆ U.
 (D2) μ(A) ≤ 2ⁿ Hⁿ(A) for Borel A ⊆ ∂*E. [Covering argument: for τ > 0 and j ∈ ℕ let A_j := {x ∈ A : μ(B̄_ρ(x)) ≤ (1 + τ)ω_nρⁿ for 0 < ρ < 1/j} (A_j ↑ A as Θⁿ(μ, ·) = 1 on A). If A_j ⊆ ⋃ᵢ Cᵢ with diam Cᵢ = dᵢ < 1/j and Cᵢ ∩ A_j ∋ xᵢ, then Cᵢ ⊆ B̄_{dᵢ}(xᵢ), so μ(A_j) ≤ Σᵢ(1 + τ)ω_n dᵢⁿ = 2ⁿ(1 + τ)Σᵢ ω_n(dᵢ/2)ⁿ; taking infima, μ(A_j) ≤ 2ⁿ(1 + τ)Hⁿ(A); let j → ∞, τ ↓ 0.] With 5a, μ ≪ σ.
 (D3) Θⁿ(σ, x) = 1 for σ-a.e. x. The set M_i := ∂*E ∩ W_i is Borel, countably n-rectifiable (5c) and Hⁿ(M_i ∩ K) ≤ μ(W̄_i) < ∞ for every compact K (D1). By the sibling tangent_characterizations (Theorem 1.6, “⇒”), for Hⁿ-a.e. x ∈ M_i, M_i has an approximate tangent space (Def. 1.4), hence (Simon Remark 1.5(3)) Hⁿ(M_i ∩ B_ρ(x))/(ω_nρⁿ) → 1; for x ∈ W_i and small ρ, M_i ∩ B_ρ(x) = ∂*E ∩ B_ρ(x). Take the union over i.
 Conclusion: μ and σ are locally finite Borel measures on U, concentrated on ∂*E (5a), mutually absolutely continuous (D1, D2). Fix i and apply the Radon-Nikodym/differentiation theorem (Simon Ch. 1, Theorems 3.23-3.24 with the Symmetric Vitali Property on ℝ^N; Mathlib Besicovitch.ae_tendsto_rnDeriv, which needs locally finite measures on all of ℝ^N) to the finite measures μ⌞W_i ≪ σ⌞W_i: (μ⌞W_i)(A) = ∫_A D dσ⌞W_i for Borel A, with D(x) = lim_{ρ↓0} μ(B̄_ρ(x))/σ(B̄_ρ(x)) for σ-a.e. x ∈ W_i (balls inside W_i); at σ-a.e. x this ratio is [μ(B̄_ρ(x))/(ω_nρⁿ)]/[σ(B̄_ρ(x))/(ω_nρⁿ)] → 1/1 (closed-ball densities equal open-ball densities since B_ρ ⊆ B̄_ρ ⊆ B_{(1+τ)ρ}). So μ⌞W_i = σ⌞W_i for every i, hence μ = σ on Borel subsets of U = ⋃_i W_i; both vanish on ℝ^N ∖ U (∂*E ⊆ U). Hence μ = Hⁿ⌞∂*E as measures on ℝ^N.

Part 6. Parts 0, 5c, 5d, 4 (with 1b) and 3f give (0), (R), (M), (‡), (‡‡). ∎

## Key steps

1. Existence from the sibling gauss_green; complement, scaling, translation and rotation invariances of Gauss-Green pairs; normalize x = 0, ν_E(0) = e_N.
2. Density estimates (1), (2), (5), (6): averages of ν_N → 1, μ(B_ρ) ≤ 2V'(ρ) and μ(B_ρ) ≤ Cρⁿ.
3. Compactness of blow-ups (translation estimate + mollification + Arzelà-Ascoli); limits are ℝⁿ × H by horizontal invariance.
4. Corrected sign (erratum): ∫_F D_Nζ ≤ 0, so F = {x_N > λ}.
5. Sobolev inequality and the density bounds (10), (11) force λ = 0; hence the full L¹_loc convergence (‡‡).
6. (‡) from (GG), the convergence (‡‡), (1) and the mass bound (6').
7. μ is concentrated on the Borel set ∂*E (Lebesgue-Besicovitch differentiation); the sibling measure lemma and density comparison give rectifiability of ∂*E.
8. Density comparisons (Hⁿ⌞∂*E ≤ μ ≤ 2ⁿHⁿ⌞∂*E), density 1 of Hⁿ⌞∂*E from Theorem 1.6 (sibling), and Radon-Nikodym give μ = Hⁿ⌞∂*E.

## Reference use

### local-project

Queries:
- `rg -n "^def |^noncomputable def |^abbrev " project/GMT/Ch03/Contract.lean (frozen definitions: IsC1Submanifold, IsPositiveLocallyIntegrableWeight, approxTangentPlane, HasTangentialDifferentialAt, areaJacobian, coareaJacobian, HasApproxTangentPlaneWithMultiplicity, coordinateProjection, frameProjection, ForAlmostAllProjections, HasLocallyFinitePerimeter, IsGaussGreenPair, normalAverage, reducedBoundary, reducedNormal)`
- `rg -n "theorem normDet_comp|def normDet|normDet_sq" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n "ae_tendsto_average_norm_sub|ae_tendsto_rnDeriv|def vitaliFamily" mathlib/Mathlib/MeasureTheory/Covering`
- `rg -n "tendstoUniformlyOn_of_ae_tendsto" mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `rg -n "exists_disjoint_covering_ae" mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n "haarMeasure_unique|isHaarMeasure_haarMeasure" mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `rg -n "eLpNorm_le_eLpNorm_fderiv_of_eq" mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `rg -n "euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "LipschitzWith.ae_differentiableAt" mathlib/Mathlib`
- `rg -n -i "lusin" mathlib/Mathlib`
- `rg -l -i "grassmannian|coarea|kirszbraun|CountablyRectifiable|whitney" mathlib/Mathlib`
- `grep -n for simon_lemma_3_2, measurable_rectifiable_purelyUnrectifiable_decomposition, countablyRectifiable_of_submanifold_cover, IsSimonSubmanifold, simon_remark_1_3_nullMeasurable, HasWeightedApproximateTangentSpaceAt.unique, rademacher_ae_differentiableAt, exists_contDiff_one_extension_of_whitney, HasWhitneyC1Compatibility, area_formula_lipschitzOn_multiplicity, weighted_area_formula_lipschitzOn_fiberSum, areaJacobian_comp_eq_parametrization_mul_tangential, simon_theorem_3_3, simon_theorem_3_6, simon_theorem_4_14, exists_isClosed_continuousOn_of_measurable, IsLocallyBV in the pinned simongmt package Poincare/SimonGMT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/RingTheory/Grassmannian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/CoordinateProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`

Snapshot (project d09bc8a, Mathlib 25730c7c) plus the pinned simongmt dependency. Available and cited by the children: SimonGMT simon_lemma_3_2 and measurable_rectifiable_purelyUnrectifiable_decomposition (Lemma 3.2), countablyRectifiable_of_submanifold_cover (1.2 '⇐'; IsSimonSubmanifold (E := ℝⁿ) 1 unfolds to the contract's IsC1Submanifold), countablyRectifiable_iUnion/_range/_of_measure_zero, countablyRectifiable_image_contDiffOn_open, HasWeightedApproximateTangentSpaceAt.unique, Lipschitz area formulas on Euclidean domains (area_formula_lipschitzOn_multiplicity, weighted_area_formula_lipschitzOn_fiberSum, injective_area_formula_lipschitzOn, aemeasurable_weightedAreaFiberSum_lipschitzOn), areaJacobian_comp_eq_parametrization_mul_tangential, rademacher_ae_differentiableAt, Whitney C¹ extension (exists_contDiff_one_extension_of_whitney / HasWhitneyC1Compatibility), density theorems simon_theorem_3_3, simon_theorem_3_6, simon_remark_3_7_of_openSigmaFinite, vector Riesz representation simon_theorem_4_14, real-valued Lusin exists_isClosed_continuousOn_of_measurable, IsLocallyBV and euclideanDivergence; Mathlib LinearMap.normDet_comp, Besicovitch.vitaliFamily with VitaliFamily.ae_tendsto_average_norm_sub and Besicovitch.ae_tendsto_rnDeriv, MeasureTheory.tendstoUniformlyOn_of_ae_tendsto (Egorov), Vitali.exists_disjoint_covering_ae, Haar measure on locally compact groups, eLpNorm_le_eLpNorm_fderiv_of_eq (Gagliardo-Nirenberg-Sobolev), EuclideanSpace.euclideanHausdorffMeasure_eq_volume, ENNReal.tsum_set_one. No match (hence supplied as shared children or proved inside children): no C¹ approximation theorem and no coarea formula beyond the linear case in SimonGMT; Mathlib has no coarea formula, no countable rectifiability, no Kirszbraun theorem, no Whitney C¹ extension (only manifold embeddings), no Lusin continuity theorem (only Lusin separation/Lusin-Souslin), no measure on Grassmannians (RingTheory/Grassmannian.lean is algebraic), no BV compactness; neither library has the Besicovitch-Federer theorem or De Giorgi's theorem. SimonGMT's Chapter03 tangentialDifferential/tangentialJacobian (Differential.lean) are not used, as the README marks them unfaithful.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
