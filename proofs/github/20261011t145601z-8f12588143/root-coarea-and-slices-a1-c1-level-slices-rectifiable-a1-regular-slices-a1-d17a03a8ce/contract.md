<!-- theorem-id: gmt-ch03/root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1.regular_slices-a1 -->

## Theorem `Submission.c1_regular_level_slice_image_countablyRectifiable`

Let m, k, N ∈ ℕ, n := m + k, D ⊆ ℝⁿ open, ψ : ℝⁿ → ℝᴺ of class C¹ on D, G : ℝⁿ → ℝᵐ of class C¹ (on all of ℝⁿ), and y ∈ ℝᵐ. Let S := {u ∈ ℝⁿ : DG(u) is surjective}. Then ψ(D ∩ S ∩ G⁻¹{y}) is countably k-rectifiable (SimonGMT CountablyRectifiable k in ℝᴺ). No assumption k > 0 or m > 0 is made. Notation: ℝ^d = Rn d = EuclideanSpace ℝ (Fin d); DG(u) = fderiv ℝ G u; D ∩ S ∩ G⁻¹{y} means (D ∩ S) ∩ G⁻¹{y}.

Node: `root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1.regular_slices-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/136

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.c1_regular_level_slice_image_countablyRectifiable`

```lean
∀ (m k N : ℕ) (D : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m) (y : Rn m), IsOpen D → ContDiffOn ℝ 1 ψ D → ContDiff ℝ 1 G → CountablyRectifiable k (ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}))
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

- Parent DAG node: `root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1.regular_slices-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent's supplied proof, step 2 (regular part). This is the implicit-function-theorem half of Simon's C¹ Sard-type Theorem 6.4 (Ch. 2 §6, chapter-02.txt lines 1476-1497): "since J_f(x) ≠ 0 precisely when df_x has rank m, the implicit function theorem implies that either f⁻¹(y) \ C is empty or else it is a k-dimensional C¹ submanifold". Here it is specialized to the image under ψ, with every detail written out. Standard background: the inverse function theorem, and the regular level set theorem (Lee, Introduction to Smooth Manifolds, 2nd ed., Cor. 5.14).

Notation: n := m + k; ℝ^d = Rn d = EuclideanSpace ℝ (Fin d); DG(u) = fderiv ℝ G u; S := {u ∈ ℝⁿ : DG(u) is surjective}. Fix y ∈ ℝᵐ. We prove that ψ(D ∩ S ∩ G⁻¹{y}) is countably k-rectifiable. The argument is uniform in m and k and needs neither k > 0 nor m > 0. For m = 0, every DG(u) is surjective. For k = 0, the parameter space ℝ⁰ is a single point.

1. (C¹ images of open subsets of ℝᵏ.) Claim: if W ⊆ ℝᵏ is open and h : ℝᵏ → ℝᴺ is C¹ on W, then h(W) is countably k-rectifiable.
   Proof. W is an open subset of ℝᵏ, so it is locally compact and σ-compact. Write W = ⋃_{j∈ℕ} C_j with each C_j ⊆ W compact. Every x ∈ W has a neighbourhood on which h is Lipschitz: h is C¹ at x because W is open, and the mean value inequality applies. So h is locally Lipschitz on the compact set C_j, and therefore Lipschitz on C_j with some constant L_j. By the Lipschitz extension theorem for maps into a finite-dimensional normed space (Mathlib LipschitzOnWith.extend_finite_dimension), there is a Lipschitz map g_j : ℝᵏ → ℝᴺ with g_j = h on C_j. Then h(W) ⊆ ⋃_j g_j(ℝᵏ), a countable union of ranges of Lipschitz maps ℝᵏ → ℝᴺ. By Definition 1.1 (countablyRectifiable_range, countablyRectifiable_iUnion, CountablyRectifiable.mono), h(W) is countably k-rectifiable. (This is SimonGMT Chapter03.countablyRectifiable_image_contDiffOn_open.)

2. (Linear algebra at a regular point.) Let u₀ ∈ D ∩ S, and let A := DG(u₀) : ℝⁿ → ℝᵐ, a surjective linear map. Put K₀ := ker A. By rank–nullity, m + dim K₀ = dim ℝⁿ = m + k, so dim K₀ = k.
   Fix a linear isomorphism ι : K₀ → ℝᵏ, and let P₀ : ℝⁿ → K₀ be the orthogonal projection onto K₀, so P₀v = v for v ∈ K₀. Set π := ι ∘ P₀ : ℝⁿ → ℝᵏ (continuous and linear) and L := (A, π) : ℝⁿ → ℝᵐ × ℝᵏ.
   L is injective: if Av = 0 and πv = 0, then v ∈ K₀, so P₀v = v and ι(v) = 0, hence v = 0. Since dim(ℝᵐ × ℝᵏ) = m + k = dim ℝⁿ, L is a linear isomorphism. In finite dimensions it is automatically a continuous linear equivalence.

3. (Chart map and inverse function theorem.) Let Φ : ℝⁿ → ℝᵐ × ℝᵏ, Φ(u) := (G(u), π(u)). Φ is C¹ on ℝⁿ with DΦ(u) = (DG(u), π) for every u. In particular DΦ(u₀) = L is invertible.
   Let V := {u ∈ ℝⁿ : DΦ(u) is a linear isomorphism ℝⁿ → ℝᵐ × ℝᵏ}. V is open: u ↦ DΦ(u) is continuous because Φ is C¹, and the invertible continuous linear maps between the Banach spaces ℝⁿ and ℝᵐ × ℝᵏ form an open set. Also u₀ ∈ V.
   Φ is C¹ with invertible derivative at u₀, so it is strictly differentiable there. The inverse function theorem gives open sets U₀ ∋ u₀ and Ω₀ ⊆ ℝᵐ × ℝᵏ such that Φ maps U₀ homeomorphically onto Ω₀. Write Θ : Ω₀ → U₀ for the inverse. Then Θ(Φ(u)) = u for u ∈ U₀, and Φ(Θ(p)) = p with Θ(p) ∈ U₀ for p ∈ Ω₀. Extend Θ arbitrarily to a map ℝᵐ × ℝᵏ → ℝⁿ. Only its values on Ω₀ are ever used; Mathlib's OpenPartialHomeomorph.symm is such a total extension.
   Moreover, Θ is C¹ at every p ∈ Ω₀ with Θ(p) ∈ V. Indeed, Φ is C¹ at Θ(p) with invertible derivative DΦ(Θ(p)). The inverse of a local homeomorphism that is C¹ with invertible derivative at the preimage point is C¹ at the image point (Mathlib OpenPartialHomeomorph.contDiffAt_symm).
   Set O := U₀ ∩ D ∩ V. Then O is open and u₀ ∈ O.

4. (The slice in the chart is a C¹ image.) Let W := {z ∈ ℝᵏ : (y, z) ∈ Ω₀ and Θ(y, z) ∈ D ∩ V}. The set Ω₀ ∩ Θ⁻¹(D ∩ V) is open, since Θ is continuous on the open set Ω₀ and D ∩ V is open. W is its preimage under the continuous map z ↦ (y, z), so W is open.
   Define h : ℝᵏ → ℝᴺ by h(z) := ψ(Θ(y, z)), using the total extension of Θ from step 3. Only z ∈ W matters, and there (y, z) ∈ Ω₀. Let z ∈ W. The map z ↦ (y, z) is C^∞. Θ is C¹ at (y, z) by step 3, since Θ(y, z) ∈ V. ψ is C¹ at Θ(y, z), because Θ(y, z) ∈ D, D is open and ψ is C¹ on D. By the chain rule, h is C¹ at z. Hence h is C¹ on W, and by step 1, h(W) is countably k-rectifiable.

5. (The chart's piece of the slice lies in h(W).) Let u ∈ O with G(u) = y. Then u ∈ U₀, so Φ(u) = (y, π(u)) ∈ Ω₀ and Θ(y, π(u)) = Θ(Φ(u)) = u ∈ D ∩ V. Thus z := π(u) ∈ W and h(z) = ψ(u). Hence ψ(O ∩ G⁻¹{y}) ⊆ h(W), and ψ(O ∩ G⁻¹{y}) is countably k-rectifiable (CountablyRectifiable.mono).

6. (Countably many charts, by Lindelöf.) By steps 2–5, every u₀ ∈ D ∩ S has an open set O_{u₀} ∋ u₀ with ψ(O_{u₀} ∩ G⁻¹{y}) countably k-rectifiable. Since ℝⁿ is second countable, there is a countable T ⊆ D ∩ S with ⋃_{u∈T} O_u = ⋃_{u∈D∩S} O_u (TopologicalSpace.isOpen_iUnion_countable). This uses only the second countability of ℝⁿ and does not use the openness of D ∩ S. (S is in fact open, since DG is continuous and surjective linear maps form an open set, but this is not needed.) Hence D ∩ S ⊆ ⋃_{u∈T} O_u, and so ψ(D ∩ S ∩ G⁻¹{y}) ⊆ ⋃_{u∈T} ψ(O_u ∩ G⁻¹{y}).

7. (Conclusion.) A countable union of countably k-rectifiable sets is countably k-rectifiable (countablyRectifiable_sUnion / countablyRectifiable_iUnion; for T = ∅ the union is the empty set, which is Hᵏ-null). A subset of a countably k-rectifiable set is countably k-rectifiable (CountablyRectifiable.mono). By steps 5–6, ψ(D ∩ S ∩ G⁻¹{y}) is countably k-rectifiable. Since y was arbitrary, the statement holds for every y ∈ ℝᵐ. ∎

Implementation notes (checked on the pinned toolchain lean 4.35.0-rc3 / Mathlib 25730c7c against `import GMT.Ch03.Submission` in the comparator's replayed Contract scope):
- `ContDiffAt.toOpenPartialHomeomorph` is not imported by Submission. Use `HasStrictFDerivAt.toOpenPartialHomeomorph Φ (ContDiffAt.hasStrictFDerivAt' hΦa hΦ'a one_ne_zero)`.
- Generalized field notation on a `ContDiffAt ℝ 1 …` hypothesis can fail, because the literal `1` makes the type unfold. Call those lemmas by their full names.
- `Poincare.SimonGMT.Chapter03.countablyRectifiable_image_contDiffOn_open` is in `Poincare.SimonGMT.Chapter03.SubmanifoldCover`, which Submission does not import. The proof below therefore inlines step 1, so no new import is needed.

Appendix: a complete Lean proof of exactly this statement. It type-checks with no warnings and depends only on [propext, Classical.choice, Quot.sound]. Place it in GMT/Ch03/Submission.lean inside `namespace GMT.Ch03`, after the frozen definitions; this is the same scope the comparator replays.

```lean
theorem Submission.c1_regular_level_slice_image_countablyRectifiable : ∀ (m k N : ℕ) (D : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m) (y : Rn m), IsOpen D → ContDiffOn ℝ 1 ψ D → ContDiff ℝ 1 G → CountablyRectifiable k (ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y})) := by
  intro m k N D ψ G y hD hψ hG
  -- C¹ images of open subsets of ℝᵏ are countably k-rectifiable
  -- (inline copy of SimonGMT `countablyRectifiable_image_contDiffOn_open`).
  have himage : ∀ (W : Set (Rn k)) (h : Rn k → Rn N), IsOpen W → ContDiffOn ℝ 1 h W →
      CountablyRectifiable k (h '' W) := by
    intro W h hW hh
    let _ : LocallyCompactSpace W := hW.locallyCompactSpace
    obtain ⟨Kc, hKc, hKcover⟩ := SigmaCompactSpace.exists_compact_covering (X := W)
    let C : ℕ → Set (Rn k) := fun j => ((↑) : W → Rn k) '' Kc j
    have hCc : ∀ j, IsCompact (C j) := fun j => (hKc j).image continuous_subtype_val
    have hCW : ∀ j, C j ⊆ W := by
      rintro j _ ⟨x, -, rfl⟩
      exact x.2
    have hLip : ∀ j, ∃ L : ℝ≥0, LipschitzOnWith L h (C j) := by
      intro j
      apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hCc j)
      intro x hx
      obtain ⟨L, t, ht, hht⟩ := (hh.contDiffAt (hW.mem_nhds (hCW j hx))).exists_lipschitzOnWith
      exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hht⟩
    choose L hL using hLip
    choose g hgL hgeq using fun j => (hL j).extend_finite_dimension
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion (fun j => range (g j))
      (fun j => Poincare.SimonGMT.Chapter03.countablyRectifiable_range (hgL j))).mono ?_
    rintro _ ⟨x, hxW, rfl⟩
    have hx : (⟨x, hxW⟩ : W) ∈ ⋃ j, Kc j := by rw [hKcover]; trivial
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨j, x, (hgeq j ⟨⟨x, hxW⟩, hj, rfl⟩).symm⟩
  -- Local charts at regular points (implicit function theorem via Φ = (G, π)).
  have hloc : ∀ u₀ : ↥(D ∩ {u | Function.Surjective (fderiv ℝ G u)}),
      ∃ O : Set (Rn (m + k)), IsOpen O ∧ (u₀ : Rn (m + k)) ∈ O ∧
        CountablyRectifiable k (ψ '' (O ∩ G ⁻¹' {y})) := by
    rintro ⟨u₀, hu₀D, hu₀S⟩
    set A : Rn (m + k) →L[ℝ] Rn m := fderiv ℝ G u₀ with hA
    have hrange : LinearMap.range (A : Rn (m + k) →ₗ[ℝ] Rn m) = ⊤ := LinearMap.range_eq_top.2 hu₀S
    set K₀ : Submodule ℝ (Rn (m + k)) := LinearMap.ker (A : Rn (m + k) →ₗ[ℝ] Rn m) with hK₀
    have hker : finrank ℝ K₀ = k := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (A : Rn (m + k) →ₗ[ℝ] Rn m)
      rw [hrange, finrank_top] at h1
      simp only [finrank_euclideanSpace, Fintype.card_fin] at h1
      change m + finrank ℝ K₀ = m + k at h1
      omega
    obtain ⟨ι⟩ : Nonempty (K₀ ≃L[ℝ] Rn k) :=
      FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simp [hker])
    let π : Rn (m + k) →L[ℝ] Rn k := (ι : K₀ →L[ℝ] Rn k).comp K₀.orthogonalProjectionOnto
    let Φ : Rn (m + k) → Rn m × Rn k := fun u => (G u, π u)
    have hΦ : ContDiff ℝ 1 Φ := hG.prodMk π.contDiff
    have hΦd : ∀ u, HasFDerivAt Φ ((fderiv ℝ G u).prod π) u := fun u =>
      ((hG.differentiable one_ne_zero u).hasFDerivAt).prodMk π.hasFDerivAt
    have hinj : Function.Injective (A.prod π) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have hAv : A v = 0 := congrArg Prod.fst hv
      have hπv : π v = 0 := congrArg Prod.snd hv
      have hvK : v ∈ K₀ := hAv
      have hP : K₀.orthogonalProjectionOnto v = ⟨v, hvK⟩ :=
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨v, hvK⟩
      have : ι ⟨v, hvK⟩ = 0 := by simpa [π, hP] using hπv
      have h0 : (⟨v, hvK⟩ : K₀) = 0 := by simpa using this
      simpa using congrArg Subtype.val h0
    have hdim : finrank ℝ (Rn (m + k)) = finrank ℝ (Rn m × Rn k) := by
      simp [Module.finrank_prod]
    let e' : Rn (m + k) ≃L[ℝ] Rn m × Rn k :=
      ((A.prod π : Rn (m + k) →ₗ[ℝ] Rn m × Rn k).linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
    have he' : (e' : Rn (m + k) →L[ℝ] Rn m × Rn k) = A.prod π := by ext1 v; rfl
    -- `V`: the open set where `DΦ` is invertible.
    let V : Set (Rn (m + k)) := (fderiv ℝ Φ) ⁻¹'
      range ((↑) : (Rn (m + k) ≃L[ℝ] Rn m × Rn k) → Rn (m + k) →L[ℝ] Rn m × Rn k)
    have hVo : IsOpen V := ContinuousLinearEquiv.isOpen.preimage (hΦ.continuous_fderiv one_ne_zero)
    have hu₀V : u₀ ∈ V := ⟨e', by rw [he', (hΦd u₀).fderiv]⟩
    have hΦa : ContDiffAt ℝ 1 Φ u₀ := hΦ.contDiffAt
    have hΦ'a : HasFDerivAt Φ (e' : Rn (m + k) →L[ℝ] Rn m × Rn k) u₀ := by
      rw [he']; exact hΦd u₀
    have hstrict := ContDiffAt.hasStrictFDerivAt' hΦa hΦ'a one_ne_zero
    let e := HasStrictFDerivAt.toOpenPartialHomeomorph Φ hstrict
    have hecoe : (e : Rn (m + k) → Rn m × Rn k) = Φ := rfl
    refine ⟨e.source ∩ D ∩ V, (e.open_source.inter hD).inter hVo,
      ⟨⟨HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hstrict, hu₀D⟩, hu₀V⟩, ?_⟩
    -- The slice through the chart is the image of the open set `W` under `h`.
    let W : Set (Rn k) := (fun z => (y, z)) ⁻¹' (e.target ∩ e.symm ⁻¹' (D ∩ V))
    have hWo : IsOpen W :=
      (e.isOpen_inter_preimage_symm (hD.inter hVo)).preimage (continuous_const.prodMk continuous_id)
    let h : Rn k → Rn N := fun z => ψ (e.symm (y, z))
    have hh : ContDiffOn ℝ 1 h W := by
      intro z hz
      apply ContDiffAt.contDiffWithinAt
      obtain ⟨hzt, hzD, ⟨L, hL⟩⟩ := hz
      have h1 : ContDiffAt ℝ 1 e.symm (y, z) := by
        refine e.contDiffAt_symm hzt (f₀' := L) ?_ ?_
        · rw [hL, hecoe]
          exact (hΦ.differentiable one_ne_zero _).hasFDerivAt
        · rw [hecoe]; exact hΦ.contDiffAt
      have h2 : ContDiffAt ℝ 1 ψ (e.symm (y, z)) := hψ.contDiffAt (hD.mem_nhds hzD)
      exact h2.comp z (h1.comp z (contDiffAt_const.prodMk contDiffAt_id))
    apply (himage W h hWo hh).mono
    rintro _ ⟨u, ⟨⟨⟨hus, huD⟩, huV⟩, huy⟩, rfl⟩
    have hey : e u = (y, π u) := by
      rw [hecoe]; simp only [Φ]; rw [show G u = y from huy]
    refine ⟨π u, ?_, ?_⟩
    · show (y, π u) ∈ e.target ∩ e.symm ⁻¹' (D ∩ V)
      rw [← hey]
      exact ⟨e.map_source hus, by rw [mem_preimage, e.left_inv hus]; exact ⟨huD, huV⟩⟩
    · show ψ (e.symm (y, π u)) = ψ u
      rw [← hey, e.left_inv hus]
  -- Lindelöf: countably many charts cover the regular part.
  choose O hOo hmem hrect using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hOo
  have hsub : ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}) ⊆
      ⋃₀ ((fun i => ψ '' (O i ∩ G ⁻¹' {y})) '' T) := by
    rintro _ ⟨u, ⟨huDS, huy⟩, rfl⟩
    have hu : u ∈ ⋃ i ∈ T, O i := by
      rw [hTU]; exact mem_iUnion.2 ⟨⟨u, huDS⟩, hmem _⟩
    obtain ⟨i, hiT, hui⟩ := mem_iUnion₂.1 hu
    exact ⟨_, ⟨i, hiT, rfl⟩, ⟨u, ⟨hui, huy⟩, rfl⟩⟩
  refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (hTc.image _) ?_).mono hsub
  rintro _ ⟨i, -, rfl⟩
  exact hrect i
```

## Key steps

1. C¹ images of open subsets of ℝᵏ are countably k-rectifiable: σ-compact exhaustion, Lipschitz on each compact piece, finite-dimensional Lipschitz extension, countable union of Lipschitz ranges.
2. At u₀ ∈ D ∩ S: K₀ = ker DG(u₀) has dimension k (rank–nullity); π := ι ∘ (orthogonal projection onto K₀) with ι : K₀ ≅ ℝᵏ; L = (DG(u₀), π) is an injective map between spaces of equal dimension, so a linear isomorphism.
3. Φ = (G, π) is C¹ with DΦ(u₀) = L invertible; V = {u : DΦ(u) invertible} is open; the inverse function theorem gives a local inverse Θ : Ω₀ → U₀, which is C¹ at points p with Θ(p) ∈ V; take the chart O := U₀ ∩ D ∩ V.
4. W := {z : (y,z) ∈ Ω₀, Θ(y,z) ∈ D ∩ V} is open, h(z) = ψ(Θ(y,z)) is C¹ on W, and ψ(O ∩ G⁻¹{y}) ⊆ h(W), so it is countably k-rectifiable.
5. Lindelöf (second countability of ℝⁿ): countably many charts O_u cover D ∩ S; a countable union plus monotonicity gives that ψ(D ∩ S ∩ G⁻¹{y}) is countably k-rectifiable.

## Reference use

### local-project

Queries:
- `rg -n "theorem isOpen_iUnion_countable" mathlib/Mathlib/Topology/Bases.lean`
- `rg -n "theorem ContDiffAt.exists_lipschitzOnWith |lemma ContDiffOn.locallyLipschitzOn" mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `rg -n "theorem OpenPartialHomeomorph.contDiffAt_symm " mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `rg -n "protected theorem ContinuousLinearEquiv.isOpen" mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `rg -n "def toOpenPartialHomeomorph|theorem mem_toOpenPartialHomeomorph_source|theorem toOpenPartialHomeomorph_coe" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `grep -n "theorem\|def \|lemma" mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `rg -n "theorem finrank_range_add_finrank_ker|noncomputable def linearEquivOfInjective" mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `rg -n "theorem FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq" mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `rg -n "theorem orthogonalProjectionOnto_mem_subspace_eq_self|def orthogonalProjectionOnto" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -l -i "countablyRectifiable" mathlib/Mathlib/MeasureTheory mathlib/Mathlib/Geometry mathlib/Mathlib/Analysis/Calculus  (no match)`
- `rg -n "hausdorffMeasure_image_null|image_null_of_locallyLipschitz|LocallyLipschitzOn.hausdorffMeasure" mathlib/Mathlib/MeasureTheory mathlib/Mathlib/Topology/MetricSpace  (no match)`
- `rg -n "theorem hausdorffMeasure_image_le \(h : LipschitzOnWith" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean; rg -n 'notation "μHE\["' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "^open|^namespace|^abbrev Rn|^def SlicesAreRectifiable" project/GMT/Ch03/Contract.lean; rg -n "^import" project/GMT/Ch03/Contract.lean`
- `rg -n "^theorem countablyRectifiable_image_contDiffOn_open|^theorem countablyRectifiable_sUnion|^theorem countablyRectifiable_iUnion|^theorem countablyRectifiable_of_measure_zero|^theorem CountablyRectifiable.mono|^theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" <pinned simongmt>/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean Chapter03/Rectifiable.lean Chapter02/Lipschitz.lean`
- `cmp GMT/Ch03/Submission.lean GMT/Ch03/Contract.lean; cmp GMT/Ch03/Contract.lean <snapshot>/project/GMT/Ch03/Contract.lean (both identical)`
- `lean Avail.lean / Avail2.lean: #check of the IFT, Lipschitz, Lindelöf and SimonGMT lemmas after only `import GMT.Ch03.Submission``
- `python3 -I: gmt-compare.py child_modules(contract mode) + lean_contract.validate_lean_statement on both child types, then `lean` on the generated NodeChallenge files`
- `lean /tmp/c1slices-decomp/Integration.lean (full child proofs + sibling stub + parent assembly + `exact Submission.X` comparator checks; #print axioms)`
- `python3 -I dag.json lean_name uniqueness (113 nodes) + grep of both names in all branches' GMT/Ch03/Submission.lean, simongmt and Mathlib (no match)`
- `sed -n 1440,1500p book/chapter-02.txt (Simon 6.2-6.4); sed -n 425,445p book/chapter-03.txt (Remark 2.10(2)); sed -n 268,290p book/chapter-02.txt (Thm 1.8)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`

Snapshot: project d09bc8a, Mathlib 25730c7c, plus the pinned simongmt package. The workspace Submission.lean and Contract.lean are byte-identical to the snapshot Contract.

No-match results:
- Mathlib has no countable-rectifiability notion; rg 'countablyRectifiable' finds nothing in MeasureTheory, Geometry or Analysis/Calculus.
- Mathlib has no lemma 'locally Lipschitz images of Hausdorff-null sets are null'.
- Mathlib has no regular-level-set rectifiability result.

Available after only `import GMT.Ch03.Submission`, verified by #check:
- Inverse function theorem: HasStrictFDerivAt.toOpenPartialHomeomorph (+ mem_toOpenPartialHomeomorph_source), ContDiffAt.hasStrictFDerivAt', OpenPartialHomeomorph.contDiffAt_symm, ContinuousLinearEquiv.isOpen.
- Lindelöf: TopologicalSpace.isOpen_iUnion_countable.
- Lipschitz: ContDiffAt.exists_lipschitzOnWith, LipschitzOnWith.extend_finite_dimension, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact.
- Linear algebra: LinearMap.finrank_range_add_finrank_ker, LinearMap.linearEquivOfInjective, FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self.
- SimonGMT: countablyRectifiable_range / _iUnion / _sUnion / _of_measure_zero, CountablyRectifiable.mono, Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn.

Not reachable without a new import:
- ContDiffAt.toOpenPartialHomeomorph.
- HasStrictFDerivAt.implicitToOpenPartialHomeomorph.
- SimonGMT Chapter03.countablyRectifiable_image_contDiffOn_open, which is in SubmanifoldCover. Child A therefore inlines its 25-line proof.

Both child types elaborate in the comparator's replayed Contract scope. Both have complete, warning-free Lean proofs using only standard axioms. The selected frozen type follows from them plus a stub of the frozen sibling type, which is the only sorryAx.

Simon Ch. 2 6.3–6.4 (chapter-02.txt lines 1476–1497) and Ch. 3 Remark 2.10(2) (chapter-03.txt lines 439–442) give exactly the regular-part / critical-part structure used.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
