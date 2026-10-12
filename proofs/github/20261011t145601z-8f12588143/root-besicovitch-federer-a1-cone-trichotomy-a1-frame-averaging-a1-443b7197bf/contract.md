<!-- theorem-id: gmt-ch03/root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1 -->

## Theorem `Submission.bf_frameAveraging_null`

Let n ≥ 1, ℓ ≥ 1, N := n + ℓ, E := ℝ^N = EuclideanSpace ℝ (Fin N), and 𝓛 := E →L[ℝ] E with the Borel σ-algebra of the norm topology. Let μ be a finite measure on E, and let Exc ⊆ E × 𝓛 and Bad ⊆ E × 𝓛 × E be measurable sets. Assume (h1): for every a ∈ E and every (n+1)-dimensional subspace H ⊆ E, Hⁿ({θ ∈ H : |θ| = 1, (a, P_H, θ) ∈ Bad}) = 0, where P_H := H.starProjection and Hⁿ = μHE[n]. Assume (h2): for every a ∈ E, every n-dimensional subspace W with (a, P_W) ∈ Exc, and every orthonormal family u_1, …, u_ℓ of vectors in W^⊥, there is j with (a, P_{W ⊔ span{u_j}}, u_j) ∈ Bad. Then for Lebesgue-a.e. v ∈ Eⁿ, if v is linearly independent then μ({a : (a, frameProjection v) ∈ Exc}) = 0. In other words, ForAlmostAllProjections N n (fun p ↦ μ{a | (a, p) ∈ Exc} = 0).

Node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/109

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/538, https://github.com/ZhengyangZhang06/gmt-formalize/issues/548

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1423, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1424, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1425, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1426, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1427, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1428, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1429, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1430

## Lean problem

Declaration: `Submission.bf_frameAveraging_null`

```lean
∀ (n ℓ : ℕ), 0 < n → 0 < ℓ → ∀ μ : Measure (Rn (n + ℓ)), IsFiniteMeasure μ → ∀ (Exc : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)))) (Bad : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) × Rn (n + ℓ))), MeasurableSet Exc → MeasurableSet Bad → (∀ (a : Rn (n + ℓ)) (H : Submodule ℝ (Rn (n + ℓ))), finrank ℝ H = n + 1 → μHE[n] {θ | θ ∈ H ∧ ‖θ‖ = 1 ∧ (a, H.starProjection, θ) ∈ Bad} = 0) → (∀ (a : Rn (n + ℓ)) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → (a, W.starProjection) ∈ Exc → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u → (∀ j, u j ∈ Wᗮ) → ∃ j, (a, (W ⊔ Submodule.span ℝ {u j}).starProjection, u j) ∈ Bad) → ForAlmostAllProjections (n + ℓ) n (fun p ↦ μ {a | (a, p) ∈ Exc} = 0)
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

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 0.2, 4.1–4.7, 1.5(b) and 5 of the supplied proof (Dall'Alba, proof of Lemma 5.6; Mattila Ch. 18; the transfer from Haar measure on O(N) to Lebesgue-a.e. frames is the parent's adaptation). The specific exceptional and bad sets of the supplied proof are replaced by the abstract measurable sets Exc and Bad. The supplied Step 4.5 (transport of goodness under h) is then replaced by applying hypothesis (h1) directly to the plane hH⁰.

Notation: N := n + ℓ, E := ℝ^N = EuclideanSpace ℝ (Fin N), x·y inner product, |·| norm, 𝓛 := E →L[ℝ] E with the Borel σ-algebra of its norm topology, g* the adjoint of g ∈ 𝓛, P_V := V.starProjection for a subspace V, Hⁿ := μHE[n]. e_1, …, e_N is the standard basis (e_{n+j} for j ∈ {1, …, ℓ} corresponds to the index Fin.natAdd n j). W₀ := span{e_1, …, e_n}, P₀ := P_{W₀}, H⁰_j := span{e_1, …, e_n, e_{n+j}} = W₀ ⊔ span{e_{n+j}}, H⁰ := H⁰_1, S⁰ := {θ ∈ H⁰ : |θ| = 1}. 𝒱 ⊆ Eⁿ = (Fin n → E) is the set of linearly independent frames, P_v := frameProjection v = P_{span v}, and λ := volume on Eⁿ (the product of the Lebesgue measures of the factors). Exc^p := {a : (a, p) ∈ Exc}.

1. The orthogonal group and its Haar measure (supplied 0.2). Let G := {g ∈ 𝓛 : g*g = 1}. Each g ∈ G is a linear isometry, since |gx|² = x·g*gx = |x|². So g is injective, hence bijective (finite dimension), with g⁻¹ = g*; thus also gg* = 1. G is a subgroup of the invertible elements of 𝓛, and g* = g⁻¹ ∈ G. G is closed in 𝓛, being the preimage of {1} under the continuous map g ↦ g*g. It is bounded (‖g‖ ≤ 1), hence compact because 𝓛 is finite-dimensional. (Lean hint: G can be realized as unitary 𝓛 for the star ring 𝓛, star = adjoint. Mathlib/Topology/Algebra/Star/Unitary.lean, which must then be imported, gives IsTopologicalGroup (unitary R) and isClosed_unitary under [ContinuousStar R]. For 𝓛 this instance is not inferred automatically; supply it from the continuity of ContinuousLinearMap.adjoint. Compactness, i.e. CompactSpace G, is not a library instance and is proved from closed + bounded as above.) Multiplication and inversion (= adjoint) are continuous. So G is a compact, second-countable, metrizable topological group; give it its Borel σ-algebra (the trace of that of 𝓛).
 There is a left-invariant Borel probability measure θ_N on G: the Haar measure normalized by θ_N(G) = 1 (Mathlib haarMeasure with K₀ = G and haarMeasure_self). θ_N is also right invariant. For k ∈ G let ρ_k be the image of θ_N under g ↦ gk⁻¹, so ρ_k(B) = θ_N(Bk). ρ_k is a finite left-invariant Borel measure, because left and right translations commute. By uniqueness of Haar measure on compact groups (Mathlib isMulInvariant_eq_smul_of_compactSpace), ρ_k = c·θ_N for a constant c ≥ 0. Comparing total masses, c = θ_N(Gk) = θ_N(G) = 1. (Equivalently, ρ_k and θ_N are left-invariant Haar probability measures, so they coincide by Mathlib Measure.isHaarMeasure_eq_of_isProbabilityMeasure.) Likewise G′ := {g ∈ G : ge_k = e_k for k = n + 2, …, N} is a closed subgroup of G, hence a compact topological group, and it carries a left- and right-invariant Borel probability measure θ′ (same argument).
 Basic facts. (F1) For g ∈ G and a subspace V, gV is a subspace with dim gV = dim V and P_{gV} = gP_Vg*: gP_Vg* is self-adjoint and idempotent, and its range is g(range P_V) = gV. (F2) If g ∈ G′ then gH⁰ = H⁰ and gS⁰ = S⁰. Indeed H⁰ = span{e_{n+2}, …, e_N}^⊥. For x ∈ H⁰ and k ≥ n + 2, gx·e_k = gx·ge_k = x·e_k = 0, so g maps H⁰ into H⁰, and onto it by dimension count; and g is isometric. (F3) The maps g ↦ gPg* (P ∈ 𝓛 fixed) and g ↦ gx (x ∈ E fixed) are continuous on G, (g, x) ↦ gx is continuous on G × E, and (g, v) ↦ g·v := (gv_1, …, gv_n) is continuous on G × Eⁿ.

2. Bad planes give bad directions (supplied 4.1). Fix a ∈ E and let g ∈ G. W := gW₀ has dimension n and P_W = gP₀g* (F1). The vectors u_j := ge_{n+j}, j ∈ {1, …, ℓ}, are orthonormal (g is isometric) and lie in W^⊥: for w₀ ∈ W₀, ge_{n+j}·gw₀ = e_{n+j}·w₀ = 0. Also W ⊔ span{u_j} = g(W₀ ⊔ span{e_{n+j}}) = gH⁰_j, so P_{W⊔span{u_j}} = gP_{H⁰_j}g* (F1). Let B_j(a) := {g ∈ G : (a, gP_{H⁰_j}g*, ge_{n+j}) ∈ Bad}. By (h2), applied to a, W and u: if (a, gP₀g*) ∈ Exc, then g ∈ B_j(a) for some j. Each B_j(a) is Borel in G, as the preimage of the measurable set Bad ⊆ E × 𝓛 × E under the continuous map g ↦ (a, gP_{H⁰_j}g*, ge_{n+j}) (F3). On these second-countable spaces the product σ-algebra is the Borel σ-algebra.

3. Reduction to j = 1 (supplied 4.3). Let σ_j ∈ G be the permutation of the basis exchanging e_{n+1} and e_{n+j} and fixing the other e_k (σ_1 := 1). Then σ_jH⁰_1 = H⁰_j and σ_je_{n+1} = e_{n+j}. Hence for g ∈ G, (gσ_j)P_{H⁰_1}(gσ_j)* = gP_{σ_jH⁰_1}g* = gP_{H⁰_j}g* (F1) and (gσ_j)e_{n+1} = ge_{n+j}. So g ∈ B_j(a) ⟺ gσ_j ∈ B_1(a), i.e. B_j(a) = B_1(a)σ_j⁻¹. By right invariance, θ_N(B_j(a)) = θ_N(B_1(a)).

4. The law of g′e_{n+1} (supplied 4.4). The sibling sphere_cap_bounds, i.e. the declaration Submission.bf_sphereCap_measure_bounds, applies to H⁰ (dimension n + 1, n ≥ 1) and gives constants c > 0, C. With ζ := e_{n+1} ∈ S⁰: Hⁿ(S⁰) ≥ Hⁿ(S⁰ ∩ B(e_{n+1}, 2)) ≥ c2ⁿ > 0. Since S⁰ ⊆ B(e_{n+1}, 3), Hⁿ(S⁰) = Hⁿ(S⁰ ∩ B(e_{n+1}, 3)) ≤ C3ⁿ < ∞. So σ̄(B) := Hⁿ(B ∩ S⁰)/Hⁿ(S⁰), for Borel B ⊆ E, is a Borel probability measure on E with σ̄(E ∖ S⁰) = 0. Let ν₀ be the image of θ′ under the continuous map g′ ↦ g′e_{n+1}; by (F2) it is a Borel probability measure on E with ν₀(E ∖ S⁰) = 0. Claim: ν₀ = σ̄.
 (a) Invariance. Let k ∈ G′ and B Borel. ν₀(k⁻¹B) = θ′({g′ : kg′e_{n+1} ∈ B}) = θ′(k⁻¹{g′ : g′e_{n+1} ∈ B}) = ν₀(B) by left invariance of θ′. Also σ̄(k⁻¹B) = Hⁿ(k⁻¹B ∩ S⁰)/Hⁿ(S⁰) = Hⁿ(k⁻¹(B ∩ S⁰))/Hⁿ(S⁰) = σ̄(B), because k⁻¹S⁰ = S⁰ (F2) and Hⁿ is invariant under the isometry k⁻¹ (Mathlib Isometry.euclideanHausdorffMeasure_image).
 (b) Transitivity. Let x, y ∈ S⁰. If x = y take k := 1. Otherwise put d := x − y ≠ 0 and k z := z − 2((z·d)/|d|²)d, the reflection in d^⊥; k ∈ G (k* = k, k² = 1). Since |x| = |y| = 1, y·d = y·x − 1 = −|d|²/2, so ky = y + d = x. For i ≥ n + 2, e_i·d = 0 (d ∈ H⁰), so ke_i = e_i and k ∈ G′.
 (c) Uniqueness. Let ν be any Borel probability measure on E with ν(E ∖ S⁰) = 0 and ν(k⁻¹B) = ν(B) for all k ∈ G′ and Borel B. Let φ : E → ℝ be bounded and continuous, and Ψ(x) := ∫_{G′}φ(g′x) dθ′(g′). By invariance, ∫_Eφ(g′x) dν(x) = ∫φ dν for each g′ ∈ G′. Integrate over g′ (θ′ is a probability) and apply Fubini to the bounded continuous function (g′, x) ↦ φ(g′x) and the finite measure θ′ ⊗ ν: ∫φ dν = ∫_{G′}∫_Eφ(g′x) dν(x) dθ′(g′) = ∫_EΨ(x) dν(x). For x, y ∈ S⁰ take k from (b); by right invariance of θ′, Ψ(x) = Ψ(ky) = ∫φ(g′ky) dθ′(g′) = ∫φ(g′y) dθ′(g′) = Ψ(y). So Ψ is constant on S⁰, equal to Ψ(e_{n+1}). As ν(E ∖ S⁰) = 0 and ν(E) = 1, ∫φ dν = Ψ(e_{n+1}), a value independent of ν. Applying this to ν₀ and σ̄ gives ∫φ dν₀ = ∫φ dσ̄ for every bounded continuous φ. Hence ν₀ = σ̄, since finite Borel measures on a metric space are determined by the integrals of bounded continuous functions (Mathlib MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure, in Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean, which must be imported).
 Consequence: for every Borel Y ⊆ E with Hⁿ(Y ∩ S⁰) = 0, θ′({g′ ∈ G′ : g′e_{n+1} ∈ Y}) = ν₀(Y) = σ̄(Y) = 0.

5. Fibres over cosets (supplied 4.5). Fix a ∈ E and h ∈ G, and let H := hH⁰. H has dimension n + 1 and P_H = hP_{H⁰}h* (F1). For g′ ∈ G′, hg′H⁰ = hH⁰ = H (F2), so (hg′)P_{H⁰}(hg′)* = P_H. Thus hg′ ∈ B_1(a) ⟺ (a, P_H, hg′e_{n+1}) ∈ Bad ⟺ g′e_{n+1} ∈ Y_h := h⁻¹(Bad_{a,H}), where Bad_{a,H} := {θ ∈ E : (a, P_H, θ) ∈ Bad} is Borel (a section of a measurable set). Y_h = h*(Bad_{a,H}) is Borel, h* being a homeomorphism. Since h⁻¹ maps S(H) := {θ ∈ H : |θ| = 1} = hS⁰ onto S⁰, Y_h ∩ S⁰ = h⁻¹(Bad_{a,H} ∩ S(H)). By isometry invariance of Hⁿ and hypothesis (h1) for a and H: Hⁿ(Y_h ∩ S⁰) = Hⁿ(Bad_{a,H} ∩ S(H)) = Hⁿ({θ | θ ∈ H ∧ |θ| = 1 ∧ (a, P_H, θ) ∈ Bad}) = 0. By step 4, θ′({g′ ∈ G′ : hg′ ∈ B_1(a)}) = θ′({g′ : g′e_{n+1} ∈ Y_h}) = 0.

6. Fubini (supplied 4.6). Let χ := 1_{B_1(a)}. The map (h, g′) ↦ χ(hg′) is Borel on G × G′, because B_1(a) is Borel and multiplication is continuous. For each g′ ∈ G′ ⊆ G, right invariance gives ∫_Gχ(hg′) dθ_N(h) = θ_N(B_1(a)g′⁻¹) = θ_N(B_1(a)). Integrate over g′ (θ′(G′) = 1) and apply Tonelli to θ_N ⊗ θ′: θ_N(B_1(a)) = ∫_{G′}∫_Gχ(hg′) dθ_N(h) dθ′(g′) = ∫_G∫_{G′}χ(hg′) dθ′(g′) dθ_N(h) = 0 by step 5. By steps 2 and 3, θ_N({g ∈ G : (a, gP₀g*) ∈ Exc}) ≤ Σ_jθ_N(B_j(a)) = ℓ·θ_N(B_1(a)) = 0. This holds for every a ∈ E.

7. Tonelli over E × G (supplied 4.7). 𝒩′ := {(a, g) ∈ E × G : (a, gP₀g*) ∈ Exc} is measurable, being the preimage of Exc under the continuous map (a, g) ↦ (a, gP₀g*). Apply Tonelli to the finite measures μ and θ_N: ∫_Gμ({a : (a, g) ∈ 𝒩′}) dθ_N(g) = ∫_Eθ_N({g : (a, g) ∈ 𝒩′}) dμ(a) = 0 by step 6. Hence μ(Exc^{gP₀g*}) = 0 for θ_N-a.e. g. The map p ↦ μ(Exc^p) is measurable on 𝓛 by the measurability part of Tonelli for the finite measure μ and the measurable set Exc (Mathlib measurable_measure_prodMk_right). So 𝒢 := {p ∈ 𝓛 : μ(Exc^p) > 0} is Borel, 𝒢̃ := {g ∈ G : gP₀g* ∈ 𝒢} is Borel, and θ_N(𝒢̃) = 0.

8. Measurability of the bad frames (supplied 1.5(b)). 𝒱 is open in Eⁿ (Mathlib isOpen_setOfPred_linearIndependent; equivalently, v ∈ 𝒱 iff the Gram determinant det(v_i·v_j) is nonzero). By the sibling frame_projection_continuous, i.e. the declaration Submission.bf_frameProjection_continuousOn, v ↦ P_v = frameProjection v is continuous on 𝒱. Hence 𝒮 := {v ∈ 𝒱 : P_v ∈ 𝒢} = 𝒱 ∩ (P|_𝒱)⁻¹(𝒢) is Borel in Eⁿ: the preimage of the Borel set 𝒢 under a map continuous on the open set 𝒱, intersected with 𝒱, is Borel (Mathlib ContinuousOn.measurable_piecewise, or directly: (P|_𝒱)⁻¹(U) is relatively open in 𝒱, hence open in Eⁿ, for every open U ⊆ 𝓛, so the class of Borel B with 𝒱 ∩ (P|_𝒱)⁻¹(B) Borel is a σ-algebra containing the open sets).

9. Transfer to frames (supplied 5.1–5.3). (a) For g ∈ G, v ↦ g·v preserves λ. On each factor, g is a linear isometry equivalence of E and so preserves its volume (Mathlib LinearIsometryEquiv.measurePreserving); hence the product map preserves λ (measurePreserving_pi). If v ∈ 𝒱 then g·v ∈ 𝒱, span(g·v) = g(span v), and P_{g·v} = gP_vg* (F1). If v ∉ 𝒱 then g·v ∉ 𝒱, as g is injective. (b) Let v ∈ 𝒱. Choose an orthonormal basis f_1, …, f_n of span v and extend it by an orthonormal basis f_{n+1}, …, f_N of (span v)^⊥. The linear map h with he_k = f_k lies in G and hW₀ = span v. So P_v = hP₀h*, and P_{g·v} = (gh)P₀(gh)* for g ∈ G. Hence {g ∈ G : g·v ∈ 𝒮} = {g : gh ∈ 𝒢̃} = 𝒢̃h⁻¹, and θ_N({g : g·v ∈ 𝒮}) = θ_N(𝒢̃) = 0 by right invariance and step 7. For v ∉ 𝒱 the set {g : g·v ∈ 𝒮} is empty, since 𝒮 ⊆ 𝒱. (c) The set {(g, v) ∈ G × Eⁿ : g·v ∈ 𝒮} is Borel (F3, step 8). By (a), λ({v : g·v ∈ 𝒮}) = λ(𝒮) for every g ∈ G. Using θ_N(G) = 1, Tonelli (θ_N finite, λ σ-finite) and (b): λ(𝒮) = ∫_Gλ({v : g·v ∈ 𝒮}) dθ_N(g) = ∫_{Eⁿ}θ_N({g : g·v ∈ 𝒮}) dλ(v) = 0.

10. Conclusion. λ(𝒮) = 0, so for λ-a.e. v ∈ Eⁿ we have v ∉ 𝒮. That is, if v is linearly independent then frameProjection v ∉ 𝒢, i.e. μ({a | (a, frameProjection v) ∈ Exc}) = 0. This is ForAlmostAllProjections (n + ℓ) n (fun p ↦ μ {a | (a, p) ∈ Exc} = 0). ∎

## Key steps

1. O(N) = {g ∈ 𝓛 : g*g = 1} is a compact metrizable group with a bi-invariant Haar probability θ_N (right invariance follows from uniqueness of Haar measure). Likewise the stabilizer O′ of e_{n+2}, …, e_N carries such a measure θ′.
2. For g ∈ O(N), W = gW₀ and u_j = ge_{n+j} fall under (h2), so {g : (a, gP₀g*) ∈ Exc} ⊆ ⋃_j B_j(a) with Borel sets B_j(a). A basis permutation and right invariance give θ_N(B_j(a)) = θ_N(B_1(a)).
3. The law of g′e_{n+1} under θ′ is normalized Hⁿ on S⁰. Here 0 < Hⁿ(S⁰) < ∞ by bf_sphereCap_measure_bounds, and uniqueness follows from invariance, transitivity via reflections, Fubini and right invariance.
4. Fibres over cosets hO′ are θ′-null by (h1) for H = hH⁰ and isometry invariance of Hⁿ. Fubini with right invariance then gives θ_N(B_1(a)) = 0, hence θ_N{g : (a, gP₀g*) ∈ Exc} = 0 for every a.
5. Tonelli over μ ⊗ θ_N gives θ_N{g : μ(Exc^{gP₀g*}) > 0} = 0, where 𝒢 = {p : μ(Exc^p) > 0} is Borel.
6. Transfer: the bad-frame set 𝒮 is Borel by bf_frameProjection_continuousOn. Lebesgue measure on frames is O(N)-invariant and θ_N{g : g·v ∈ 𝒮} = 0 for every v, so Tonelli gives λ(𝒮) = 0.

## Reference use

### local-project

Queries:
- `cat manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n "^noncomputable def frameProjection|^def ForAlmostAllProjections|^abbrev Rn" project/GMT/Ch03/Contract.lean`
- `rg -n "instance instMeasurableSpace|instBorelSpace" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `rg -n "IsTopologicalGroup \(unitary|isClosed_unitary" mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `rg -l "CompactSpace \(unitary|instance.*CompactSpace.*orthogonalGroup" mathlib/Mathlib (no match)`
- `rg -n "isMulInvariant_eq_smul_of_compactSpace|isHaarMeasure_eq_of_isProbabilityMeasure" mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `rg -n "theorem haarMeasure_self" mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `rg -n "μHE\[|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement" mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n "theorem ae_tendsto_measure_inter_div" mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n "ext_of_forall_integral_eq_of_IsFiniteMeasure|ext_of_forall_lintegral_eq_of_IsFiniteMeasure" mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `rg -n "measurable_measure_prodMk_left|measurable_measure_prodMk_right" mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `rg -n "theorem hausdorffMeasure_image_le" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n "exists_isClosed_sdiff_lt|exists_isClosed_diff_lt" mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n "theorem isClosedMap_fst_of_compactSpace" mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `grep -n isOpen_setOf_linearIndependent mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n "theorem inverse_continuousAt" mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `rg -n "theorem measurePreserving" mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; rg -n "theorem measurePreserving_pi" mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `rg -n "theorem addHaar_ball" mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n "theorem finrank_add_finrank_orthogonal" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `rg -n "theorem ContinuousOn.measurable_piecewise" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `rg -n "theorem lintegral_liminf_le" mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `grep -n "theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `grep dag.json for bf_coneExceptional_measurableSet, bf_sphereCap_measure_bounds, bf_sphere_ae_slabGood, bf_slabGood_imp_coneTrichotomy, bf_frameProjection_continuousOn, bf_frameAveraging_null (no match)`
- `lake env lean GMT/Scratch/ConeTrichotomySplitElab.lean and GMT/Scratch/ConeTrichotomySplitAssembly.lean (comparator scope: all child types elaborate; the parent assembly compiles without sorry)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ConeTrichotomySplitElab.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ConeTrichotomySplitAssembly.lean`

The snapshot fixes Rn, frameProjection and ForAlmostAllProjections (Contract.lean lines 56, 129, 138); the child types use them verbatim. Mathlib supplies every library ingredient that the child proofs cite: the Borel structure on E →L[ℝ] E (ContinuousLinearMap.instMeasurableSpace/instBorelSpace); the Haar measure with haarMeasure_self, and its uniqueness on compact groups (isMulInvariant_eq_smul_of_compactSpace, isHaarMeasure_eq_of_isProbabilityMeasure); and the unitary-group topology (IsTopologicalGroup (unitary R), isClosed_unitary), which needs a ContinuousStar instance on 𝓛 supplied locally from the continuity of the adjoint. It also supplies Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume, the Lipschitz image bound (LipschitzOnWith.hausdorffMeasure_image_le; SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn), Vitali.exists_disjoint_subfamily_covering_enlargement, Besicovitch.ae_tendsto_measure_inter_div and MeasurableSet.exists_isClosed_sdiff_lt. Further cited results are measurable_measure_prodMk_left/right, isClosedMap_fst_of_compactSpace, isOpen_setOfPred_linearIndependent, NormedRing.inverse_continuousAt, LinearIsometryEquiv.measurePreserving, measurePreserving_pi, MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure, ContinuousOn.measurable_piecewise, Measure.addHaar_ball and Submodule.finrank_add_finrank_orthogonal. The searches found no CompactSpace instance for O(N), no Haar measure on O(N) and no Besicovitch–Federer material, so frame_averaging builds these itself. No existing declaration states any of the six children, and all six names are fresh in dag.json.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
