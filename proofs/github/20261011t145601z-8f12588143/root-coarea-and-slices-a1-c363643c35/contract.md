<!-- theorem-id: gmt-ch03/root.coarea_and_slices-a1 -->

## Theorem `Submission.coareaFormula_and_slices_hold`

Let m, k, ℓ ∈ ℕ with k > 0, n := m + k, M ⊆ ℝ^{n+ℓ} countably n-rectifiable, U ⊇ M open and f : ℝ^{n+ℓ} → ℝᵐ locally Lipschitz on U. (CoareaFormula) If moreover M is Hⁿ-measurable and θ is a positive locally integrable weight on M, then with J*^M_f(x) := coareaJacobian (approxTangentPlane n M θ x) f x: (a) for Hⁿ-a.e. x ∈ M there are P and L with HasWeightedApproximateTangentSpaceAt n M θ x P and HasTangentialDifferentialAt P f x L; (b) ∫_A J*^M_f dHⁿ = ∫_{ℝᵐ} Hᵏ(A ∩ f⁻¹{y}) dLᵐ(y) and (c) ∫_A g·J*^M_f dHⁿ = ∫_{ℝᵐ} ∫_{A ∩ f⁻¹{y}} g dHᵏ dLᵐ(y) for every Hⁿ-measurable A ⊆ M and every Hⁿ⌞A-measurable g : ℝ^{n+ℓ} → [0, ∞]. (SlicesAreRectifiable) If M is Hⁿ-measurable, then M ∩ f⁻¹{y} is countably k-rectifiable for Lᵐ-a.e. y ∈ ℝᵐ.

Node: `root.coarea_and_slices-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/25, https://github.com/ZhengyangZhang06/gmt-formalize/issues/21, https://github.com/ZhengyangZhang06/gmt-formalize/issues/22, https://github.com/ZhengyangZhang06/gmt-formalize/issues/24

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/132, https://github.com/ZhengyangZhang06/gmt-formalize/issues/133, https://github.com/ZhengyangZhang06/gmt-formalize/issues/134, https://github.com/ZhengyangZhang06/gmt-formalize/issues/135, https://github.com/ZhengyangZhang06/gmt-formalize/issues/136, https://github.com/ZhengyangZhang06/gmt-formalize/issues/137, https://github.com/ZhengyangZhang06/gmt-formalize/issues/138, https://github.com/ZhengyangZhang06/gmt-formalize/issues/139, https://github.com/ZhengyangZhang06/gmt-formalize/issues/140, https://github.com/ZhengyangZhang06/gmt-formalize/issues/141

## Lean problem

Declaration: `Submission.coareaFormula_and_slices_hold`

```lean
CoareaFormula ∧ SlicesAreRectifiable
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
- Child DAG node: `root.coarea_and_slices-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 3, (2.7)-(2.9) and Remark 2.10(2), chapter-03.txt lines 412-442 (printed p. 77): “This follows from the C¹ case (see §6 of Ch. 2) by using the decomposition M = ∪M_j of Remark 1.3 and the C¹ Approximation Theorem 1.5 of Ch. 2 in a similar manner to the procedure used for the discussion of the area formula above” (lines 426-428), and 2.10(2) “follows directly from the decomposition … together with the C¹ Sard-type Theorem 6.4 of Ch. 2 and the C¹ Approximation Theorem 1.5” (lines 440-442). The C¹ case is Ch. 2, (6.3), (6.4), (6.6) (chapter-02.txt lines 1410-1510, printed pp. 65-67), whose proof Simon does not give (“See [Har79] or [Fed69] for the details”, p. 66). Departures, stated explicitly: (i) we supply a proof of the needed C¹ coarea formula, in parameter form (Lemma L3 below, following the standard proof of [Fed69, 3.2.12, 3.2.22] / Evans-Gariepy, Thm 3.11: implicit function theorem + Fubini on the regular set, a covering argument on the critical set); (ii) the null parts of the decomposition, which Simon passes over, are handled by Eilenberg's inequality (sibling eilenberg_inequality = Simon Ch. 2, 1.9); (iii) erratum in (2.9) (README): the domains are A on both sides (printed ∫_A on the left and f⁻¹(y) ∩ M on the right).

Notation. n = m + k with k ≥ 1; N := n + ℓ; ℝ^d = EuclideanSpace ℝ (Fin d); Hˢ = μHE[s] (on ℝ^N or ℝⁿ as indicated); Lᵈ = volume on ℝ^d. For x ∈ M: T_xM := approxTangentPlane n M θ x, d^Mf_x := tangentialDifferential T_xM f x, J*^M_f(x) := coareaJacobian T_xM f x = normDet((d^Mf_x)*). For a linear L, normDet is Mathlib's LinearMap.normDet (|det| in orthonormal bases when source and range dimensions agree; normDet_comp: normDet(g∘f) = normDet(g.domRestrict(range f))·normDet(f)). For C¹ ψ, Jψ(u) := normDet(Dψ(u)).

Statement. CoareaFormula ∧ SlicesAreRectifiable (see the Lean statement): for m, k, ℓ with k > 0, M ⊆ ℝ^N countably (m+k)-rectifiable, U ⊇ M open, f : ℝ^N → ℝᵐ locally Lipschitz on U: (CO) if moreover M is H^{m+k}-measurable and θ is a positive locally integrable weight on M, then (a) for Hⁿ-a.e. x ∈ M there are P, L with HasWeightedApproximateTangentSpaceAt n M θ x P and HasTangentialDifferentialAt P f x L; (b) ∫_A J*^M_f dHⁿ = ∫_{ℝᵐ} Hᵏ(A ∩ f⁻¹{y}) dLᵐ(y) and (c) ∫_A g·J*^M_f dHⁿ = ∫_{ℝᵐ}∫_{A∩f⁻¹{y}} g dHᵏ dLᵐ(y) for Hⁿ-measurable A ⊆ M and Hⁿ⌞A-measurable g ≥ 0; (SL) if M is Hⁿ-measurable (not used), then M ∩ f⁻¹{y} is countably k-rectifiable for Lᵐ-a.e. y.

Part 0. Preliminaries.

0.1 Case m = 0. Then ℝᵐ = ℝ⁰ = {0}, L⁰ is the unit point mass, f⁻¹{0} = ℝ^N and n = k. Every linear map into ℝ⁰ is 0, its adjoint is the zero map ℝ⁰ → T_xM, whose normDet is 1 (empty determinant), so J*^M_f ≡ 1; (b), (c) read ∫_A g dHⁿ = ∫_A g dHⁿ; (SL) says M itself is countably n-rectifiable (hypothesis); (a) is proved in 1.2 below (it does not use m ≥ 1). Assume m ≥ 1 in Lemmas L1-L3.

0.2 Null sets have null slices (from the sibling eilenberg_inequality, Simon Ch. 2, 1.9). (i) If Z ⊆ U with Hⁿ(Z) = 0, then Hᵏ(Z ∩ f⁻¹{y}) = 0 for Lᵐ-a.e. y. Proof: U is covered by countably many open balls B_b on which f is Lipschitz; extend f|B_b to a Lipschitz f_b : ℝ^N → ℝᵐ (Simon Ch. 2, 1.2, coordinatewise). Eilenberg's inequality for Z ∩ B_b, f_b, gives a Borel g_b ≥ Hᵏ(Z ∩ B_b ∩ f_b⁻¹{y}) with ∫ g_b ≤ C·Lip(f_b)ᵐ·Hⁿ(Z ∩ B_b) = 0, so g_b = 0 a.e.; as f = f_b on B_b, Hᵏ(Z ∩ B_b ∩ f⁻¹{y}) = 0 for a.e. y; take the countable union. (ii) The same holds in parameter space: if O ⊆ ℝⁿ is open, G : O → ℝᵐ is locally Lipschitz and Z ⊆ O is Lⁿ-null then Hᵏ(Z ∩ G⁻¹{y}) = 0 for a.e. y (same proof with N := n; Lⁿ(Z) = 0 gives μHE[m+k](Z) = 0 on ℝ^{m+k} by EuclideanSpace.euclideanHausdorffMeasure_eq_volume).

Part L. The C¹ case (Simon Ch. 2, (6.3)-(6.6), in parameter form).

L1 (critical slices; Simon's consequence of 6.3 stated before 6.4: “Hᵏ(C ∩ f⁻¹(y)) = 0 for Lᵐ-a.e. y”). Let O ⊆ ℝⁿ be open, G : O → ℝᵐ C¹, C := {u ∈ O : rank DG(u) < m} (relatively closed in O, rank being lower semicontinuous). Then Hᵏ(C ∩ G⁻¹{y}) = 0 for Lᵐ-a.e. y.
Proof. O is a countable union of closed cubes Q₀ ⊆ O; fix one, of side a, and Λ := max_{Q₀}‖DG‖. For j ≥ 1 choose an integer M_j ≥ j such that, with s_j := a/M_j, ‖DG(u) − DG(u')‖ ≤ 1/j for u, u' ∈ Q₀, |u − u'| ≤ √n s_j (uniform continuity). Divide Q₀ into M_jⁿ closed subcubes Q of side s_j. If Q ∩ C ≠ ∅ pick u_Q ∈ Q ∩ C; the range of DG(u_Q) lies in a hyperplane H_Q of ℝᵐ. By the mean value inequality, for u ∈ Q, G(u) = G(u_Q) + DG(u_Q)(u − u_Q) + e with |e| ≤ √n s_j/j and |DG(u_Q)(u − u_Q)| ≤ Λ√n s_j; hence G(Q) lies in a set {v : |p_{H_Q}(v − G(u_Q))| ≤ (Λ + 1)√n s_j, |p_{H_Q^⊥}(v − G(u_Q))| ≤ √n s_j/j}, so Lᵐ(G(Q)) ≤ C₂ s_jᵐ/j with C₂ := 2ω_{m−1}((Λ + 1)√n)^{m−1}√n. Let g_j(y) := Σ_{Q∩C≠∅} c_k(√n s_j)^k 1_{G(Q∩C)}(y) (G(Q ∩ C) is compact; c_k as in the definition of H^k_δ, cf. eilenberg_inequality). Since C ∩ Q₀ ∩ G⁻¹{y} is covered by the subcubes Q (diameter √n s_j) with y ∈ G(Q ∩ C), H^k_{√n s_j}(C ∩ Q₀ ∩ G⁻¹{y}) ≤ g_j(y), while ∫ g_j dLᵐ ≤ M_jⁿ c_k n^{k/2} s_j^k C₂ s_jᵐ/j = c_k n^{k/2} C₂ aⁿ/j → 0. With g := liminf g_j (Borel), Hᵏ(C ∩ Q₀ ∩ G⁻¹{y}) ≤ g(y) and ∫ g ≤ liminf ∫ g_j = 0 (Fatou), so g = 0 a.e. ∎

Convention for L2-L3: fix a linear isometry e : ℝᵐ × ℝᵏ → ℝⁿ (Euclidean product, e.g. via finSumFinEquiv) and identify ℝᵐ × ℝᵏ with ℝⁿ through e; e maps Lᵐ ⊗ Lᵏ to Lⁿ, and |det DΦ(u)| denotes the absolute Jacobian determinant of the map ℝⁿ → ℝⁿ, u ↦ e(Φ(u)) (this is what LA computes in orthonormal bases).

L2 (regular points; Simon p. 66: “the implicit function theorem implies that … f⁻¹(y) ∖ C … is a k-dimensional C¹ submanifold”). Let O, G be as in L1 and u₀ ∈ O ∖ C. Let K₀ := ker DG(u₀) (dimension k) and π := ι∘p_{K₀} : ℝⁿ → ℝᵏ with ι : K₀ → ℝᵏ a linear isometry. Then Φ := (G, π) : O → ℝᵐ × ℝᵏ (≅ ℝⁿ) has invertible DΦ(u₀) (if DG(u₀)v = 0 and πv = 0 then v ∈ K₀ and v = 0). By the inverse function theorem there is an open O' ∋ u₀, O' ⊆ O ∖ C, such that Φ|O' is a C¹ diffeomorphism onto an open Ω with DΦ(u) invertible on O'. For y ∈ ℝᵐ put Ω_y := {z : (y, z) ∈ Ω} (open); then O' ∩ G⁻¹{y} = {Φ⁻¹(y, z) : z ∈ Ω_y}, and z ↦ Φ⁻¹(y, z) is C¹ and injective on Ω_y with derivative E_u := DΦ(u)⁻¹|_{{0}×ℝᵏ} (u = Φ⁻¹(y, z)), an isomorphism of ℝᵏ onto ker DG(u) (DG(u)E_u = 0, πE_u = id).

LA (linear algebra). Let A : ℝⁿ → T be a linear isomorphism onto an n-dimensional inner product space T, Γ : ℝⁿ → ℝᵐ surjective, K := ker Γ, π : ℝⁿ → ℝᵏ with π|K invertible, E := (π|K)⁻¹ : ℝᵏ → K, and Λ := Γ∘A⁻¹ : T → ℝᵐ. Then normDet(A∘E)·|det(Γ, π)| = normDet(Λ*)·normDet(A).
Proof. Use orthonormal bases adapted to ℝⁿ = K^⊥ ⊕ K, T = A(K) ⊕ A(K)^⊥, ℝᵐ × ℝᵏ. (Γ, π) is block lower triangular ((Γ, π)|K = (0, π|K)), so |det(Γ, π)| = |det(Γ|K^⊥)|·|det(π|K)| = |det(Γ|K^⊥)|/|det E|. By normDet_comp, normDet(A∘E) = normDet(A|K)·|det E| (range E = K). A is block upper triangular w.r.t. (K ⊕ K^⊥) → (A(K) ⊕ A(K)^⊥) with diagonal blocks A|K and A₂₂ := p_{A(K)^⊥}∘A|K^⊥, so normDet(A) = normDet(A|K)·|det A₂₂|. Since ker Λ = A(K), Γ|K^⊥ = Λ∘A|K^⊥ = Λ|_{A(K)^⊥}∘A₂₂, so |det(Γ|K^⊥)| = |det(Λ|_{A(K)^⊥})|·|det A₂₂|, and |det(Λ|_{A(K)^⊥})| = normDet(Λ*) (Λ* is an isomorphism of ℝᵐ onto (ker Λ)^⊥ = A(K)^⊥, adjoint to Λ|_{A(K)^⊥}). Multiplying: normDet(A∘E)|det(Γ, π)| = normDet(A|K)·normDet(Λ*)·|det A₂₂| = normDet(Λ*)·normDet(A). ∎

L3 (C¹ coarea formula in parameter form = Simon Ch. 2, (6.3), (6.6) for the submanifold ψ(D) and g = G∘ψ⁻¹, transported by the area formula). Let D ⊆ ℝⁿ be open, ψ : ℝⁿ → ℝ^N C¹ on a neighbourhood of D̄, injective and bi-Lipschitz on D with Dψ(u) injective, and G : ℝⁿ → ℝᵐ C¹. For u ∈ D let T_u := range Dψ(u), Λ_u := DG(u)∘(Dψ(u))⁻¹ : T_u → ℝᵐ and J*(u) := normDet(Λ_u*). Then for every Lⁿ-measurable B ⊆ D and Borel φ : ℝ^N → [0, ∞]: the function y ↦ ∫_{ψ(B∩G⁻¹{y})} φ dHᵏ is Lᵐ-a.e. measurable and
 ∫_B φ(ψ(u)) J*(u) Jψ(u) du = ∫_{ℝᵐ} ∫_{ψ(B∩G⁻¹{y})} φ dHᵏ dLᵐ(y).
Proof. (a) Critical part, B ⊆ C := {u ∈ D : rank DG(u) < m}: Λ_u is not surjective, so Λ_u* is not injective and J*(u) = 0; the left side is 0. By L1, Hᵏ(C ∩ G⁻¹{y}) = 0 for a.e. y, and ψ is Lipschitz on D, so Hᵏ(ψ(B ∩ G⁻¹{y})) = 0 and the right integrand vanishes a.e. (b) B ⊆ O' for O', Φ, Ω, E_u as in L2: put B' := Φ(B) (Lebesgue measurable) and B'_y := {z : (y, z) ∈ B'}. Write B' = B'' ∪ Z'' with B'' Borel and Lⁿ(Z'') = 0; by Tonelli Lᵏ((Z'')_y) = 0 for Lᵐ-a.e. y, so for those y the section B'_y is Lᵏ-measurable. For each such y, ψ(B ∩ G⁻¹{y}) = χ_y(B'_y) with χ_y(z) := ψ(Φ⁻¹(y, z)), a C¹ injective immersion of Ω_y with Dχ_y(z) = Dψ(u)E_u. By the injective area formula on the k-dimensional parameter domain (Simon Ch. 2, (3.2), (4.13); SimonGMT injective/weighted area formulas for Lipschitz maps, applied on countably many compact pieces of Ω_y where χ_y is Lipschitz), ∫_{χ_y(B'_y)} φ dHᵏ = ∫_{B'_y} φ(χ_y(z)) normDet(Dψ(u)E_u) dz. By Tonelli on ℝᵐ × ℝᵏ (which also gives the a.e.-measurability in y) and the change of variables formula for the C¹ diffeomorphism Φ:
 ∫_{ℝᵐ}∫_{ψ(B∩G⁻¹{y})} φ dHᵏ dy = ∫_{B'} φ(ψ(Φ⁻¹(y, z))) normDet(Dψ(u)E_u)|_{u=Φ⁻¹(y,z)} d(y, z) = ∫_B φ(ψ(u)) normDet(Dψ(u)E_u)|det DΦ(u)| du,
 and LA (with A = Dψ(u), Γ = DG(u)) turns the integrand into φ(ψ(u)) J*(u) Jψ(u). (c) General B: D ∖ C is covered by countably many O'_t as in L2 (Lindelöf); B = (B ∩ C) ⊔ ⨆_t B_t with B_t := (B ∩ O'_t) ∖ ⋃_{t'<t} O'_{t'}. The left side is countably additive in B. On the right, for each y the sets ψ(B_t ∩ G⁻¹{y}) are pairwise disjoint (ψ injective); writing B_t = B_t^b ∪ Z_t with B_t^b Borel and Lⁿ(Z_t) = 0, the sets ψ(B_t^b ∩ G⁻¹{y}) are Borel (ψ restricted to each compact subset of D is a homeomorphism onto its image, and D is σ-compact), and Hᵏ(ψ(Z_t ∩ G⁻¹{y})) = 0 for a.e. y by 0.2(ii) and the Lipschitz bound for ψ. Hence for a.e. y, ∫ over ψ(B ∩ G⁻¹{y}) is the sum of the integrals over the pieces, and (a), (b) and monotone convergence give the formula. ∎

Part 1. The coarea formula for M (CO).

1.1 Good chart balls. Exactly as in the area formula (Simon Remark 1.3 and Lemma 1.2 via the sibling submanifold_cover; Lindelöf): countably many (ψ_α, D_α), α ∈ ℕ, D_α an open ball with closure in the chart domain, ψ_α C¹ near D̄_α, injective and bi-Lipschitz on D_α with injective derivative, ψ_α(D̄_α) ⊆ B_{s_α}(x_α) ⊆ U where f is Lipschitz on B_{s_α}(x_α), and M ⊆ N₀ ∪ ⋃_α ψ_α(D_α), Hⁿ(N₀) = 0 (choose the balls so that their interiors already cover V ∩ ψ⁻¹(U) for each chart V). h_α := f∘ψ_α is Lipschitz on D_α.

1.2 Pointwise identification and (a). Apply the sibling chart_tangent_differential to (M, U, θ, f) and the chart of α: there is an Lⁿ-null Z_α ⊆ D_α such that for u ∈ D_α ∖ Z_α with x := ψ_α(u) ∈ M: HasWeightedApproximateTangentSpaceAt n M θ x T_u (T_u := range Dψ_α(u)), h_α is differentiable at u, and HasLineDerivAt ℝ f (Dh_α(u)w) x (Dψ_α(u)w) for all w. As in the area formula (uniqueness of weighted tangent planes, SimonGMT HasWeightedApproximateTangentSpaceAt.unique, θ(x) > 0; uniqueness of line derivatives) T_xM = T_u and d^Mf_x = L_x where L_x∘Dψ_α(u) = Dh_α(u). Hence J*^M_f(x) = normDet(L_x*). Conclusion (a) holds off the Hⁿ-null set N₀ ∪ ⋃_α ψ_α(Z_α) with P := T_u, L := L_x.

1.3 C¹ approximation (Simon line 427). Extend h_α|D̄_α to a Lipschitz h̃_α : ℝⁿ → ℝᵐ (Simon Ch. 2, 1.2, coordinatewise). By the sibling c1_approximation, for i ≥ 1 there is a C¹ G_{α,i} : ℝⁿ → ℝᵐ with Lⁿ({h̃_α ≠ G_{α,i}} ∪ {Dh̃_α ≠ DG_{α,i}}) < 1/i. Let E_{α,i} := {u ∈ D_α ∖ Z_α : h̃_α differentiable at u, h̃_α(u) = G_{α,i}(u), Dh̃_α(u) = DG_{α,i}(u)}. Then Lⁿ(D_α ∖ ⋃ᵢ E_{α,i}) = 0, and for u ∈ E_{α,i}: h_α(u) = G_{α,i}(u), Dh_α(u) = DG_{α,i}(u) (u is interior to D_α), so L_x = DG_{α,i}(u)∘(Dψ_α(u))⁻¹ = Λ_u for G := G_{α,i}, ψ := ψ_α, and J*^M_f(ψ_α(u)) = J*(u) in the notation of L3.

1.4 Decomposition. Let A ⊆ M be Hⁿ-measurable and g ≥ 0 Hⁿ⌞A-measurable; choose Borel g' with g = g' Hⁿ⌞A-a.e. Put A_α := (A ∩ ψ_α(D_α)) ∖ ⋃_{β<α} ψ_β(D_β), B_α := D_α ∩ ψ_α⁻¹(A_α) (Lⁿ-measurable), B_{α,i} := (B_α ∩ E_{α,i}) ∖ ⋃_{i'<i} E_{α,i'}, A_{α,i} := ψ_α(B_{α,i}). Then A = A_null ⊔ ⨆_{α,i} A_{α,i} with A_null ⊆ (A ∩ N₀) ∪ ⋃_α ψ_α(D_α ∖ ⋃_i E_{α,i}) Hⁿ-null, the A_{α,i} pairwise disjoint and Hⁿ-measurable, and A_{α,i} ∩ f⁻¹{y} = ψ_α(B_{α,i} ∩ G_{α,i}⁻¹{y}) (for u ∈ B_{α,i}, f(ψ_α(u)) = h_α(u) = G_{α,i}(u)).

1.5 One piece. L3 with D := D_α, ψ := ψ_α, G := G_{α,i}, B := B_{α,i}, φ := g' gives ∫_{B_{α,i}} g'(ψ_α u) J*(u) Jψ_α(u) du = ∫_{ℝᵐ}∫_{A_{α,i}∩f⁻¹{y}} g' dHᵏ dy (inner function a.e. measurable). By 1.3 and the injective weighted area formula for ψ_α on B_{α,i} (as in the area formula), the left side equals ∫_{A_{α,i}} g'·J*^M_f dHⁿ (in particular J*^M_f is Hⁿ⌞A-measurable, being a.e. equal on each A_{α,i} to the transport of the measurable J* by the bi-Lipschitz ψ_α).

1.6 Summation. Summing over (α, i) (monotone convergence on both sides; A_null contributes 0 on the left):
 ∫_A g'·J*^M_f dHⁿ = ∫_{ℝᵐ} Σ_{α,i} ∫_{A_{α,i}∩f⁻¹{y}} g' dHᵏ dy.
 For Lᵐ-a.e. y: Hᵏ(A_null ∩ f⁻¹{y}) = 0 (0.2(i)); each A_{α,i} ∩ f⁻¹{y} is the union of a Borel set and an Hᵏ-null set (write B_{α,i} = Borel ∪ Lⁿ-null set Z' and use 0.2(ii) for Z' and G_{α,i}, then the Lipschitz bound for ψ_α); so Σ_{α,i}∫_{A_{α,i}∩f⁻¹{y}} g' dHᵏ = ∫_{A∩f⁻¹{y}} g' dHᵏ. Finally {g ≠ g'} ∩ A is Hⁿ-null, so it does not change the left side and, by 0.2(i), its slices are Hᵏ-null for a.e. y, so g' may be replaced by g on the right. This proves (c) (Simon (2.9) with the corrected domain A), and (b) (Simon (2.8)) is the case g ≡ 1. Together with 1.2 this proves CoareaFormula.

Part 2. Slices (SL) (Simon Remark 2.10(2), lines 439-442).

2.1 With (ψ_α, D_α), h̃_α, G_{α,i} as in 1.1, 1.3 (Z_α is not needed here; replace E_{α,i} by E'_{α,i} := D_α ∩ {h̃_α = G_{α,i}}), Lⁿ(D_α ∖ ⋃_i E'_{α,i}) = 0, and M ⊆ M_null ∪ ⋃_{α,i} ψ_α(E'_{α,i}) with M_null := (M ∩ N₀) ∪ ⋃_α ψ_α(D_α ∖ ⋃_i E'_{α,i}) Hⁿ-null. For every y, M ∩ f⁻¹{y} ⊆ (M_null ∩ f⁻¹{y}) ∪ ⋃_{α,i} ψ_α(E'_{α,i} ∩ G_{α,i}⁻¹{y}). No measurability of M is used.

2.2 Fix (α, i), G := G_{α,i}, C := {u ∈ D_α : rank DG(u) < m}. (R) For every y, (D_α ∖ C) ∩ G⁻¹{y} is covered by countably many sets O'_t ∩ G⁻¹{y} = {Φ_t⁻¹(y, z) : z ∈ (Ω_t)_y} (L2), so ψ_α((D_α ∖ C) ∩ G⁻¹{y}) ⊆ ⋃_t ψ_α∘Φ_t⁻¹(y, ·)((Ω_t)_y), a countable union of images of open subsets of ℝᵏ under C¹ maps, each countably k-rectifiable (SimonGMT Chapter03.countablyRectifiable_image_contDiffOn_open, with dimension k); this is the regular part of Simon's C¹ Sard-type Theorem 6.4. (C) By L1, Hᵏ(C ∩ G⁻¹{y}) = 0 for Lᵐ-a.e. y, hence Hᵏ(ψ_α(C ∩ G⁻¹{y})) = 0 (ψ_α Lipschitz on D_α); this is the critical part of 6.4.

2.3 Conclusion. By 0.2(i), Hᵏ(M_null ∩ f⁻¹{y}) = 0 for Lᵐ-a.e. y. Let Y be the complement of the union of the countably many exceptional Lᵐ-null sets from 2.2(C) and 0.2(i). For y ∈ Y, M ∩ f⁻¹{y} is contained in the union of an Hᵏ-null set and countably many countably k-rectifiable sets, hence is countably k-rectifiable (SimonGMT countablyRectifiable_of_measure_zero, countablyRectifiable_iUnion, CountablyRectifiable.mono). This proves SlicesAreRectifiable (for m = 0 it is the hypothesis, cf. 0.1). ∎

## Key steps

1. m = 0 is trivial (J* ≡ 1, L⁰ a point mass); null sets have Hᵏ-null slices for a.e. y by the sibling Eilenberg inequality.
2. L1: critical slices Hᵏ(C ∩ G⁻¹{y}) = 0 a.e. for C¹ G (covering argument).
3. L2/LA/L3: implicit function theorem, a linear-algebra identity for coarea factors, Fubini and change of variables give the C¹ coarea formula in parameter form (Simon Ch. 2 (6.3), (6.6)).
4. Good chart balls via Lemma 1.2 (sibling); identification of T_xM and d^Mf_x via the sibling chart lemma, giving (a).
5. C¹ approximation (sibling) of f∘ψ_α on pieces where values and derivatives agree, so J*^M_f∘ψ_α equals the parameter coarea factor.
6. Apply L3 on each piece, sum, and discard null pieces (Eilenberg) to get (b), (c).
7. Slices: regular parts of level sets are C¹ images of open subsets of ℝᵏ (countably k-rectifiable), critical parts and null parts have Hᵏ-null slices for a.e. y.

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
