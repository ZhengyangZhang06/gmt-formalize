<!-- theorem-id: gmt-ch03/root.chart_tangent_differential-a1.chart_blowup_tangent-a1 -->

## Theorem `Submission.chartTD_biLipschitz_chart_approx_tangent`

Let n, N ∈ ℕ, B ⊆ ℝⁿ open, ψ : ℝⁿ → ℝ^N of class C¹ on B, K-Lipschitz on B (K ∈ ℝ≥0), and c > 0 with c|u − u'| ≤ |ψ(u) − ψ(u')| for all u, u' ∈ B. Then for every u ∈ B the set ψ(B) has approximate tangent space T := range Dψ(u) at ψ(u) in the sense of Simon's Definition 1.4 (HasApproximateTangentSpaceAt n (ψ(B)) (ψ(u)) T): finrank T = n and lim_{λ↓0} ∫_{η_{ψ(u),λ}(ψ(B))} f dHⁿ = ∫_T f dHⁿ for every f ∈ C_c(ℝ^N, ℝ).

Node: `root.chart_tangent_differential-a1.chart_blowup_tangent-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/24

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/96

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/489, https://github.com/ZhengyangZhang06/gmt-formalize/issues/490, https://github.com/ZhengyangZhang06/gmt-formalize/issues/491, https://github.com/ZhengyangZhang06/gmt-formalize/issues/492

## Lean problem

Declaration: `Submission.chartTD_biLipschitz_chart_approx_tangent`

```lean
∀ (n N : ℕ) (B : Set (Rn n)) (ψ : Rn n → Rn N) (K : ℝ≥0) (c : ℝ), IsOpen B → ContDiffOn ℝ 1 ψ B → LipschitzOnWith K ψ B → 0 < c → (∀ u ∈ B, ∀ u' ∈ B, c * ‖u - u'‖ ≤ ‖ψ u - ψ u'‖) → ∀ u ∈ B, HasApproximateTangentSpaceAt n (ψ '' B) (ψ u) (LinearMap.range (fderiv ℝ ψ u).toLinearMap)
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

- Parent DAG node: `root.chart_tangent_differential-a1`
- Child DAG node: `root.chart_tangent_differential-a1.chart_blowup_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof Step 3, (P4), together with the scaling identity (F1) and the area formula fact (Σ2). This is the step 'since x ∈ N_j and N_j is a C¹ submanifold, lim_{λ↓0} ∫_{η_{x,λ}(N_j)} f dHⁿ = ∫_{T_xN_j} f dHⁿ' of Simon's proof of Theorem 1.6 '⇒' (chapter-03.txt lines 113-143; Remark 1.5(2), lines 87-90), proved for a single bi-Lipschitz chart with the area formula (Simon Ch. 2, (3.1), (3.2), (3.5)). Uses the sibling blowup_scaling. Import note: the SimonGMT area formula on a Lipschitz domain lives in Poincare.SimonGMT.Chapter02.AreaDomain, which GMT.Ch03.Submission does not import; the formalization adds `import Poincare.SimonGMT.Chapter02.AreaDomain` (prebuilt, pinned package; the verifier allows extra imports in the Submission and new files under GMT/Ch03/, and the frozen statements elaborate identically with it). Every other lemma cited is available after `import GMT.Ch03.Submission`.

Notation. Γ := ψ(B), x := ψ(u), L := Dψ(u) = fderiv ℝ ψ u, T := range L, Jψ(v) := normDet(Dψ(v)) = √det(Dψ(v)*Dψ(v)) (Mathlib LinearMap.normDet of fderiv ℝ ψ v), J := Jψ(u), Lⁿ = volume on ℝⁿ, Hⁿ = μHE[n], ω_n := Lⁿ(B̄_1(0)) ∈ (0, ∞).

1. Differentiability. As B is open and ψ is C¹ on B, ψ is differentiable at every v ∈ B with derivative Dψ(v), and v ↦ Dψ(v) is continuous on B. Since ψ is K-Lipschitz on the open set B, ‖Dψ(v)‖ ≤ K for v ∈ B: for w ∈ ℝⁿ and all small t > 0 we have v + tw ∈ B and |ψ(v + tw) − ψ(v)| ≤ Kt|w|; divide by t and let t ↓ 0.

2. Dimension of T. For w ∈ ℝⁿ and small t > 0 (so that u + tw ∈ B), ct|w| ≤ |ψ(u + tw) − ψ(u)|; dividing by t and letting t ↓ 0 gives c|w| ≤ |Lw|. Hence L is injective and finrank T = finrank ℝⁿ = n (LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin).

3. Jacobian facts. (a) normDet is continuous on the space of linear maps ℝⁿ → ℝ^N: normDet(A) ≥ 0 and normDet(A)² = det(A*A) (ContinuousLinearMap.normDet_sq), so normDet(A) = √det(A*A) is a composition of continuous maps (adjoint, composition, determinant on the finite-dimensional space of endomorphisms of ℝⁿ, square root). With step 1, Jψ is continuous on B; and Jψ = normDet ∘ (fderiv ℝ ψ) is Borel on all of ℝⁿ (measurable_fderiv). (b) For every linear A : ℝⁿ → ℝ^N, normDet(A) ≤ ‖A‖ⁿ: by the linear area formula (Simon Ch. 2, (3.1); Mathlib LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume) Hⁿ(A(E)) = normDet(A)·Lⁿ(E) for every E ⊆ ℝⁿ; taking E = B̄_1(0) and using that A is ‖A‖-Lipschitz (SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn, Hⁿ = Lⁿ on ℝⁿ) gives normDet(A)ω_n ≤ ‖A‖ⁿω_n with 0 < ω_n < ∞. With step 1, 0 ≤ Jψ(v) ≤ Kⁿ for every v ∈ B.

4. Area formula on Γ, in measure form. Γ is Borel: B is a Borel subset of the Polish space ℝⁿ and ψ is continuous and injective on B (lower bound, c > 0), so Γ = ψ(B) is Borel by the Lusin-Souslin theorem (Mathlib MeasurableSet.image_of_continuousOn_injOn). Let ν_B be Lebesgue measure on B with density Jψ, ν_B(E) = ∫_{B ∩ E} Jψ dLⁿ (Mathlib (volume.restrict B).withDensity of the measurable NNReal-valued function Jψ, step 3(a)); ψ is a.e.-measurable for ν_B (continuous on the open set B, which carries ν_B). Claim: ψ_#ν_B = Hⁿ⌞Γ. Let E' ⊆ ℝ^N be Borel and apply the weighted area formula on a Lipschitz domain (Simon Ch. 2, (3.5) with (3.2); SimonGMT Chapter02.weighted_area_formula_lipschitzOn_fiberSum) with s = B (open, hence null-measurable), the K-Lipschitz map ψ and the weight w := 1_{E'}∘ψ (measurable on B since ψ is continuous there). Because ψ is injective on B, the fibre sum weightedAreaFiberSum B ψ w y = Σ_{v ∈ B, ψ(v) = y} w(v) equals 1 if y ∈ Γ ∩ E' and 0 otherwise; and because B is open, fderivWithin ℝ ψ B v = Dψ(v) (fderivWithin_of_isOpen), so SimonGMT's areaJacobianWithin ψ B v = Jψ(v). The formula therefore reads Hⁿ(Γ ∩ E') = ∫_{B ∩ ψ⁻¹(E')} Jψ dLⁿ = (ψ_#ν_B)(E'). Hence Hⁿ⌞Γ = ψ_#ν_B as Borel measures. Consequently, for every continuous g : ℝ^N → ℝ, ∫_Γ g dHⁿ = ∫ g d(ψ_#ν_B) = ∫ g∘ψ dν_B = ∫_B g(ψ(v)) Jψ(v) dv (Mathlib integral_map and integral_withDensity_eq_integral_smul; these identities hold without any integrability assumption, both sides being 0 for non-integrable g).

5. Fix f ∈ C_c(ℝ^N, ℝ). Choose R > 0 with f = 0 outside B_R(0) (f has compact support) and put ‖f‖ := sup|f| < ∞. For λ > 0 let g_λ(z) := f(η_{x,λ}(z)) = f((z − x)/λ); g_λ is continuous, |g_λ| ≤ ‖f‖, and g_λ = 0 outside B_{Rλ}(x). By the sibling scaling identity (blowup_scaling with A = Γ, g = f), ∫_{η_{x,λ}(Γ)} f dHⁿ = λ^{-n}∫_Γ g_λ dHⁿ. By step 4 (g = g_λ), I(λ) := ∫_{η_{x,λ}(Γ)} f dHⁿ = λ^{-n}∫_{ℝⁿ} F_λ(v) dv, where F_λ(v) := 1_B(v)·f((ψ(v) − x)/λ)·Jψ(v) (∫_B = ∫ of the indicator, B being measurable).

6. Substitution v = u + λy. For λ > 0, ∫_{ℝⁿ} F_λ(u + λy) dy = λ^{-n}∫_{ℝⁿ} F_λ(v) dv, by translation invariance of Lⁿ and Lⁿ(λE) = λⁿLⁿ(E) (Mathlib MeasureTheory.Measure.integral_comp_smul and integral_add_left_eq_self; valid for every function). Hence I(λ) = ∫_{ℝⁿ} G_λ(y) dy with G_λ(y) := 1_B(u + λy)·f((ψ(u + λy) − ψ(u))/λ)·Jψ(u + λy).

7. Domination. By step 3, |G_λ(y)| ≤ ‖f‖Kⁿ. If G_λ(y) ≠ 0, then u + λy ∈ B and |ψ(u + λy) − ψ(u)| < Rλ, so cλ|y| ≤ |ψ(u + λy) − ψ(u)| < Rλ, i.e. |y| < R/c. Thus |G_λ| ≤ ‖f‖Kⁿ·1_{B_{R/c}(0)} for every λ > 0, an Lⁿ-integrable bound independent of λ. Each G_λ is measurable (B is open, ψ is continuous on B, Jψ is Borel, f is continuous).

8. Pointwise limit. Fix y ∈ ℝⁿ. As λ ↓ 0: u + λy ∈ B for all small λ (B open, u ∈ B); (ψ(u + λy) − ψ(u))/λ → Ly (differentiability of ψ at u; for y = 0 both sides are 0); hence f((ψ(u + λy) − ψ(u))/λ) → f(Ly) by continuity of f; and Jψ(u + λy) → Jψ(u) = J by continuity of Jψ on B (step 3(a)). So G_λ(y) → J·f(Ly).

9. Dominated convergence along λ ↓ 0 (the filter 𝓝[>]0 is countably generated; Mathlib tendsto_integral_filter_of_dominated_convergence) yields I(λ) → J∫_{ℝⁿ} f(Ly) dy.

10. Identification of the limit. By the linear area formula, Hⁿ(L(E)) = J·Lⁿ(E) for every E ⊆ ℝⁿ. For Borel E' ⊆ ℝ^N, injectivity of L and T = L(ℝⁿ) give T ∩ E' = L(L⁻¹(E')), so (Hⁿ⌞T)(E') = J·Lⁿ(L⁻¹(E')) = J·(L_#Lⁿ)(E'). Thus Hⁿ⌞T = J·L_#Lⁿ as measures, and ∫_T f dHⁿ = J∫_{ℝⁿ} f(Ly) dy (integral against a constant multiple of a measure and change of variables for the push-forward under the continuous map L; f∘L is bounded, continuous, and vanishes outside {y : |Ly| < R} ⊆ B_{R/c}(0) by step 2, so it is integrable).

11. By steps 9 and 10, lim_{λ↓0} ∫_{η_{x,λ}(Γ)} f dHⁿ = ∫_T f dHⁿ for every f ∈ C_c(ℝ^N, ℝ); with step 2 this is HasApproximateTangentSpaceAt n Γ x T. (For n = 0: ℝ⁰ = {0}, B = {u}, Γ = {x}, T = {0}, L⁰ is the unit point mass, H⁰ is counting measure and J = 1; every step above remains valid. If n > N the hypotheses are contradictory by step 2, since no injective linear map ℝⁿ → ℝ^N exists.) ∎

## Key steps

1. ‖Dψ‖ ≤ K on B (Lipschitz on an open set) and c|w| ≤ |Dψ(u)w| (lower bound), so finrank range Dψ(u) = n.
2. Jψ = normDet∘Dψ is Borel, continuous on B, and 0 ≤ Jψ ≤ Kⁿ (linear area formula + Lipschitz image bound).
3. Injective weighted area formula on the open B (SimonGMT weighted_area_formula_lipschitzOn_fiberSum, import Chapter02.AreaDomain): Hⁿ⌞ψ(B) = ψ_#(Jψ·Lⁿ⌞B), hence ∫_{ψ(B)} g dHⁿ = ∫_B (g∘ψ)Jψ for continuous g.
4. Scaling identity (sibling) and the substitution v = u + λy turn ∫_{η_{x,λ}(ψ(B))} f dHⁿ into ∫ G_λ(y) dy.
5. G_λ is dominated by ‖f‖Kⁿ1_{B_{R/c}(0)} and converges pointwise to Jψ(u) f(Dψ(u)y); dominated convergence.
6. Linear area formula: Hⁿ⌞range L = J·L_#Lⁿ, so the limit equals ∫_{range Dψ(u)} f dHⁿ.

## Reference use

### local-project

Queries:
- `rg -n "^def |^noncomputable def |^abbrev " project/GMT/Ch03/Contract.lean (Rn, IsPositiveLocallyIntegrableWeight, HasTangentialDifferentialAt; contract scope replayed via verifier/gmt-compare.py contract_scope)`
- `grep -n "def blowUpMap|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt|IsLocallyIntegrableMultiplicity" simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn "theorem simon_theorem_3_6|simon_remark_3_7_of_openSigmaFinite|ae_dimensionalUpperDensity_eq_zero_outside_of_openSigmaFinite|def dimensionalUpperDensity|def dimensionalDensityQuotient|def IsBorelRegularOuterMeasure|def IsOpenSigmaFinite|measure_toOuterMeasure_isBorelRegular|realUnitBallVolume_pos" simongmt/Poincare/SimonGMT/Chapter01`
- `grep -rn "injective_area_formula_lipschitzOn|weighted_area_formula_lipschitzOn_fiberSum|def weightedAreaFiberSum|def areaFiber|areaJacobianWithin|euclideanHausdorffMeasure_image_le_of_lipschitzOn|nullMeasurableSet_image_of_lipschitzOn|rademacher_ae_differentiableAt|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure" simongmt/Poincare/SimonGMT/Chapter02`
- `rg -n "euclideanHausdorffMeasure_homothety_image|euclideanHausdorffMeasure_homothety_preimage|euclideanHausdorffMeasure_smul₀|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n "normDet_sq|euclideanHausdorffMeasure_image_eq_normDet_mul_volume|hausdorffMeasure_image" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n "ae_tendsto_average_norm_sub|tendsto_filterAt|ae_tendsto_rnDeriv" mathlib/Mathlib/MeasureTheory/Covering`
- `rg -n "ae_differentiableWithinAt_of_mem|LipschitzWith.ae_differentiableAt" mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `rg -n "isOpen_biUnion_countable|ae_ball_iff|isCompact_closure|addHaar_closedBall|image_of_continuousOn_injOn|exists_antilipschitzWith|finrank_range_of_inj|integral_inter_add_sdiff₀|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|exists_measurable_subset_ae_eq|ContDiffAt.exists_lipschitzOnWith|continuousOn_fderiv_of_isOpen|lipschitzOnWith_of_nnnorm_fderiv_le|tendsto_integral_filter_of_dominated_convergence|integral_comp_smul|integral_withDensity_eq_integral_smul|measurable_fderiv" mathlib/Mathlib`
- `lake env lean GMT/Scratch/ChartCheckAvail*.lean (#check availability of every cited lemma after `import GMT.Ch03.Submission`)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`

Snapshot manifest: project d09bc8a (Contract.lean byte-identical to the workspace), Mathlib 25730c7c, plus the pinned simongmt package. Found and cited by the children: SimonGMT blowUpMap, HasApproximateTangentSpaceAt (Def. 1.4) and HasWeightedApproximateTangentSpaceAt (Def. 1.7). Also cited: SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn (F2) and nullMeasurableSet_image_of_lipschitzOn (Simon 1.8(i)), and weighted_area_formula_lipschitzOn_fiberSum (injective area formula on an open Lipschitz domain; needs import Chapter02.AreaDomain). Also: the density machinery ae_dimensionalUpperDensity_eq_zero_outside_of_openSigmaFinite / simon_remark_3_7_of_openSigmaFinite (Simon 1.3.6, 3.7(2); needs import Chapter01.DensityComparison), with measure_toOuterMeasure_isBorelRegular and simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure (needs import Chapter02.AreaLiteral). Mathlib: euclideanHausdorffMeasure_homothety_image/_preimage, Isometry.euclideanHausdorffMeasure_image, LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume, ContinuousLinearMap.normDet_sq, VitaliFamily.ae_tendsto_average_norm_sub with Besicovitch.vitaliFamily/tendsto_filterAt, and LipschitzOnWith.ae_differentiableWithinAt_of_mem (Rademacher). Further Mathlib lemmas: MeasurableSet.image_of_continuousOn_injOn (Lusin-Souslin), Measure.addHaar_closedBall, LinearMap.exists_antilipschitzWith, Convex.lipschitzOnWith_of_nnnorm_fderiv_le, ContDiffAt.exists_lipschitzOnWith, tendsto_integral_filter_of_dominated_convergence, Measure.integral_comp_smul, integral_withDensity_eq_integral_smul, TopologicalSpace.isOpen_biUnion_countable and ae_ball_iff. Every Mathlib lemma cited is visible after `import GMT.Ch03.Submission` (checked with #check). No match in the snapshot for: a ready-made 'C¹ chart image has the classical tangent plane as approximate tangent space' lemma, a weighted locality lemma for approximate tangent planes, a blow-up change-of-variables lemma for blowUpMap, or a ρⁿ-normalized Lebesgue-point lemma for Hⁿ⌞S. These are supplied as children blowup_scaling, chart_blowup_tangent, weighted_tangent_combination and lebesgue_points. SimonGMT's Chapter03 Differential.lean tangential notions are not used.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
