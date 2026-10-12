<!-- theorem-id: gmt-ch03/root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_good_directions-a1 -->

## Theorem `Submission.bf_sphere_ae_slabGood`

Let n ≥ 1, ℓ ∈ ℕ, E := ℝ^{n+ℓ}, H ⊆ E a subspace of dimension n + 1 with orthogonal projection p_H := H.starProjection, A ⊆ E compact with Hⁿ(A) < ∞, δ > 0 and a ∈ E. For θ ∈ E and s > 0 let Z_θ(s) := {x : |p_H(x − a) − (p_H(x − a)·θ)θ| < s|p_H(x − a)|} and m′(θ, r, s) := Hⁿ(A ∩ (Z_θ(s) ∩ B(a, r))). Call θ good if one of the following holds. (Ψ0) For every c > 0 there is ε > 0 with m′(θ, r, s) ≤ c(rs)ⁿ for all 0 < s < ε and 0 < r < δ. (Ψ∞) For every K ∈ ℝ and ε > 0 there are 0 < s < ε and 0 < r < δ with K(rs)ⁿ ≤ m′(θ, r, s). (Ax′) Some b ∈ A has b ≠ a, |b − a| < δ and p_H(b − a) − (p_H(b − a)·θ)θ = 0. Numerical bounds are compared in [0, ∞] via ENNReal.ofReal, and Hⁿ = μHE[n]. Then Hⁿ({θ ∈ H : |θ| = 1 and θ is not good}) = 0.

Node: `root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_good_directions-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/109

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/538

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1259, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1260, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1261

## Lean problem

Declaration: `Submission.bf_sphere_ae_slabGood`

```lean
∀ (n ℓ : ℕ), 0 < n → ∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 → ∀ A : Set (Rn (n + ℓ)), IsCompact A → μHE[n] A < ∞ → ∀ δ : ℝ, 0 < δ → ∀ a : Rn (n + ℓ), μHE[n] {θ | θ ∈ H ∧ ‖θ‖ = 1 ∧ ¬ ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μHE[n] (A ∩ ({x | ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖ < s * ‖H.starProjection (x - a)‖} ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖ < s * ‖H.starProjection (x - a)‖} ∩ Metric.ball a r))) ∨ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ H.starProjection (b - a) - inner ℝ (H.starProjection (b - a)) θ • θ = 0)} = 0
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
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_good_directions-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 2.0, 2.2–2.6 of the supplied proof (Dall'Alba, Theorem 4.16 on the sphere; Mattila Ch. 18), written at a general vertex a; the supplied text has a = 0 with A′ = A − a, and all its arguments are applied verbatim with x − a in place of x. Notation: E := ℝ^{n+ℓ}, x·y inner product, |·| norm, B(x, ρ)/B̄(x, ρ) open/closed balls, Hⁿ := μHE[n], p_H := H.starProjection, S(H) := {θ ∈ H : |θ| = 1}, ofReal := ENNReal.ofReal. For θ ∈ E and s > 0, Z_θ(s) := {x : |p_H(x − a) − (p_H(x − a)·θ)θ| < s|p_H(x − a)|} and m′(θ, r, s) := Hⁿ(A ∩ (Z_θ(s) ∩ B(a, r))). θ is good if Ψ0(θ) ∨ Ψ∞(θ) ∨ Ax′(θ), where
 Ψ0(θ): ∀c > 0 ∃ε > 0 ∀s ∈ (0, ε) ∀r ∈ (0, δ): m′(θ, r, s) ≤ ofReal(c(rs)ⁿ);
 Ψ∞(θ): ∀K ∈ ℝ ∀ε > 0 ∃s ∈ (0, ε) ∃r ∈ (0, δ): ofReal(K(rs)ⁿ) ≤ m′(θ, r, s);
 Ax′(θ): ∃b ∈ A with b ≠ a, dist(b, a) < δ and p_H(b − a) − (p_H(b − a)·θ)θ = 0.
For y ∈ E and a unit vector θ put d(y, θ) := |y − (y·θ)θ|. This is the distance from y to the line ℝθ, since |y − tθ|² = |y|² − 2t(y·θ) + t² is minimal at t = y·θ. Hence d(ty, θ) = |t|d(y, θ), and d(ξ, θ)² = 1 − (ξ·θ)² for unit ξ.

0. The measure σ_H and the constants. S(H) is closed, hence Borel. σ_H := Hⁿ restricted to S(H), i.e. σ_H(Y) = Hⁿ(Y ∩ S(H)) for every Y ⊆ E, is a Borel measure on E. By the sibling sphere_cap_bounds, i.e. the declaration Submission.bf_sphereCap_measure_bounds (H has dimension n + 1, n ≥ 1), there are c₁ > 0 and C₁ with (a) c₁ρⁿ ≤ σ_H(B(ζ, ρ)) for ζ ∈ S(H) and 0 < ρ ≤ 2, and (b) σ_H(B(ζ, ρ)) ≤ C₁ρⁿ for ζ ∈ S(H) and ρ > 0. S(H) is nonempty (dim H ≥ 1). For any ζ₀ ∈ S(H), S(H) ⊆ B(ζ₀, 3), so σ_H(E) ≤ C₁3ⁿ < ∞; thus σ_H is finite. For θ ∈ S(H) and 0 < ρ ≤ 1: 0 < c₁ρⁿ ≤ σ_H(B(θ, ρ)) ≤ σ_H(B̄(θ, ρ)) ≤ σ_H(B(θ, 2ρ)) ≤ 2ⁿC₁ρⁿ.

1. An outer measure on S(H). For E′ ⊆ S(H) let Λ(E′) := {x ∈ E : p_H(x − a) ≠ 0 and (p_H(x − a)/|p_H(x − a)| ∈ E′ or −p_H(x − a)/|p_H(x − a)| ∈ E′)} and μ(E′) := sup_{0<r<δ} r^{−n}Hⁿ(A ∩ B(a, r) ∩ Λ(E′)) ∈ [0, ∞]. Then μ(∅) = 0 and μ is monotone. μ is countably subadditive: Λ(⋃_i E_i) = ⋃_i Λ(E_i), and for each r, r^{−n}Hⁿ(A ∩ B(a, r) ∩ ⋃_iΛ(E_i)) ≤ Σ_i r^{−n}Hⁿ(A ∩ B(a, r) ∩ Λ(E_i)) ≤ Σ_i μ(E_i); now take the supremum over r. By definition, Hⁿ(A ∩ B(a, r) ∩ Λ(E′)) ≤ rⁿμ(E′) for every r ∈ (0, δ).

2. The axis set. Let C := {θ ∈ S(H) : Ax′(θ)}. For integers j ≥ 1 let K_j := {(θ, b) ∈ S(H) × A : 1/j ≤ |b − a| ≤ δ − 1/j and p_H(b − a) − (p_H(b − a)·θ)θ = 0}. K_j is a closed subset of the compact set S(H) × A (continuous conditions), hence compact, so its first projection π₁(K_j) is compact. Since b ≠ a and |b − a| < δ iff 1/j ≤ |b − a| ≤ δ − 1/j for some j ≥ 1, C = ⋃_j π₁(K_j). So C is σ-compact, hence Borel. Claim: μ(E′) = 0 for every E′ ⊆ S(H) ∖ C. Let r ∈ (0, δ) and suppose x ∈ A ∩ B(a, r) ∩ Λ(E′). Then y := p_H(x − a) ≠ 0, and θ := εy/|y| ∈ E′ for some sign ε ∈ {1, −1}. Then x ≠ a, |x − a| < r < δ, and y = ε|y|θ, so y − (y·θ)θ = 0 (θ is a unit vector). Hence Ax′(θ) holds with b := x, i.e. θ ∈ C, which contradicts θ ∈ E′ ⊆ S(H) ∖ C. So A ∩ B(a, r) ∩ Λ(E′) = ∅ for all r ∈ (0, δ), and μ(E′) = 0. In particular μ(S(H) ∖ C) = 0.

3. Caps versus slab cones. (a) For unit vectors ξ, θ: d(ξ, θ) ≤ |ξ − θ| (θ ∈ ℝθ). If moreover ξ·θ ≥ 0, then |ξ − θ|² = 2 − 2ξ·θ ≤ 2 − 2(ξ·θ)² = 2d(ξ, θ)², since 0 ≤ ξ·θ ≤ 1; hence |ξ − θ| ≤ 2d(ξ, θ). (b) For θ ∈ S(H) and s > 0, Z_θ(s) ⊆ Λ(S(H) ∩ B(θ, 2s)). If x ∈ Z_θ(s), then y := p_H(x − a) ≠ 0 (otherwise the strict inequality would read 0 < 0). Let ξ := εy/|y| with the sign ε ∈ {±1} chosen so that ξ·θ ≥ 0; then ξ ∈ S(H) (y ∈ H) and |ξ − θ| ≤ 2d(ξ, θ) = 2d(y, θ)/|y| < 2s. (c) For θ ∈ S(H) and t > 0, Λ(S(H) ∩ B(θ, t)) ⊆ Z_θ(t). If y := p_H(x − a) ≠ 0 and ξ := ±y/|y| ∈ B(θ, t), then d(y, θ) = |y|d(ξ, θ) ≤ |y||ξ − θ| < t|y|.
 Say θ ∈ S(H) satisfies (α) if for every c > 0 there is η > 0 with μ(S(H) ∩ B(θ, t)) ≤ ofReal(ctⁿ) for all t ∈ (0, η). Say it satisfies (β) if for every K ∈ ℝ and η > 0 there is t ∈ (0, η) with μ(S(H) ∩ B(θ, t)) > ofReal(Ktⁿ).
 (α) ⇒ Ψ0(θ): given c > 0 take η for c2^{−n} and put ε := η/2. For s ∈ (0, ε) and r ∈ (0, δ), by (b) and step 1, m′(θ, r, s) ≤ Hⁿ(A ∩ B(a, r) ∩ Λ(S(H) ∩ B(θ, 2s))) ≤ rⁿμ(S(H) ∩ B(θ, 2s)) ≤ rⁿc2^{−n}(2s)ⁿ = c(rs)ⁿ, because 2s < η.
 (β) ⇒ Ψ∞(θ): let K ∈ ℝ and ε > 0. If K ≤ 0, any s ∈ (0, ε), r ∈ (0, δ) work, since ofReal(K(rs)ⁿ) = 0. If K > 0, take t ∈ (0, ε) with μ(S(H) ∩ B(θ, t)) > Ktⁿ. By definition of the supremum there is r ∈ (0, δ) with r^{−n}Hⁿ(A ∩ B(a, r) ∩ Λ(S(H) ∩ B(θ, t))) > Ktⁿ. By (c), m′(θ, r, t) ≥ Hⁿ(A ∩ B(a, r) ∩ Λ(S(H) ∩ B(θ, t))) > K(rt)ⁿ. Take s := t.

4. Density dichotomy. Claim: if F ⊆ S(H) is Borel with μ(F) = 0, then the set of θ ∈ F at which neither (α) nor (β) holds is σ_H-null.
 (i) Reduction to closed F. σ_H is a finite Borel measure on the metric space E, hence weakly regular, and closed inner approximation holds (Mathlib MeasurableSet.exists_isClosed_sdiff_lt). So for each k ∈ ℕ there is a closed F̃_k ⊆ F with σ_H(F ∖ F̃_k) < 1/(k+1), and F ∖ ⋃_k F̃_k is σ_H-null. Also μ(F̃_k) ≤ μ(F) = 0. Since (α) and (β) are properties of θ alone, the exceptional set of F is contained in (F ∖ ⋃_kF̃_k) ∪ ⋃_k(exceptional set of F̃_k). So it suffices to treat closed F; from now on F ⊆ S(H) is closed with μ(F) = 0.
 (ii) For integers j ≥ 1 let F_j := {θ ∈ F : μ(S(H) ∩ B(θ, t)) ≤ jtⁿ for all t ∈ (0, 1/j)}. F_j is closed. Let θ_i ∈ F_j with θ_i → θ; then θ ∈ F. Given t ∈ (0, 1/j) and τ > 0 with t + τ < 1/j, for large i we have |θ_i − θ| < τ, so B(θ, t) ⊆ B(θ_i, t + τ) and μ(S(H) ∩ B(θ, t)) ≤ j(t + τ)ⁿ. Letting τ ↓ 0 gives μ(S(H) ∩ B(θ, t)) ≤ jtⁿ. If (β) fails at θ ∈ F, there are K ∈ ℝ and η > 0 with μ(S(H) ∩ B(θ, t)) ≤ ofReal(Ktⁿ) for all t ∈ (0, η). Then θ ∈ F_j for every integer j ≥ max(K, 1/η, 1), since for t ∈ (0, 1/j) ⊆ (0, η), ofReal(Ktⁿ) ≤ jtⁿ. So it suffices to prove, for each j, that (α) holds at σ_H-a.e. θ ∈ F_j.
 (iii) Covering estimate. Fix j, θ ∈ F_j and t ∈ (0, 1/(10j)). Let R := (S(H) ∩ B(θ, t)) ∖ F_j. As μ(F_j) ≤ μ(F) = 0, subadditivity gives μ(S(H) ∩ B(θ, t)) ≤ μ(R) + μ(F_j) = μ(R). If R = ∅ then μ(S(H) ∩ B(θ, t)) = 0. Otherwise, for ζ ∈ R put s_ζ := dist(ζ, F_j)/2. Since F_j is closed, ζ ∉ F_j and θ ∈ F_j, we get 0 < s_ζ ≤ |ζ − θ|/2 < t/2. Moreover B(ζ, s_ζ) ⊆ B(θ, 2t) ∖ F_j: for x ∈ B(ζ, s_ζ), |x − θ| < s_ζ + t < 2t and dist(x, F_j) ≥ 2s_ζ − |x − ζ| > 0. By the Vitali covering lemma (Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement applied to the balls B(ζ, s_ζ), ζ ∈ R, with radii in (0, t/2] and τ := 2) there is R′ ⊆ R with two properties. First, the balls B(ζ, s_ζ), ζ ∈ R′, are pairwise disjoint. Second, every ζ ∈ R has some ζ′ ∈ R′ with B(ζ, s_ζ) ∩ B(ζ′, s_ζ′) ≠ ∅ and s_ζ ≤ 2s_ζ′, so |ζ − ζ′| < s_ζ + s_ζ′ ≤ 3s_ζ′ < 5s_ζ′. R′ is countable, being a family of pairwise disjoint nonempty open sets in the separable space E. For ζ ∈ R′, dist(ζ, F_j) = 2s_ζ < 5s_ζ, so there is φ ∈ F_j with |ζ − φ| < 5s_ζ. Then B(ζ, 5s_ζ) ⊆ B(φ, 10s_ζ) with 10s_ζ < 5t < 1/j. Hence μ(S(H) ∩ B(ζ, 5s_ζ)) ≤ μ(S(H) ∩ B(φ, 10s_ζ)) ≤ j(10s_ζ)ⁿ ≤ j10ⁿc₁^{−1}σ_H(B(ζ, s_ζ)), by step 0(a) applied with ζ ∈ S(H) and 0 < s_ζ < 2. R ⊆ ⋃_{ζ∈R′}(S(H) ∩ B(ζ, 5s_ζ)). Apply countable subadditivity of μ, then use that the Borel sets B(ζ, s_ζ), ζ ∈ R′, are disjoint subsets of B(θ, 2t) ∖ F_j: μ(R) ≤ Σ_{ζ∈R′} j10ⁿc₁^{−1}σ_H(B(ζ, s_ζ)) = j10ⁿc₁^{−1}σ_H(⋃_{ζ∈R′}B(ζ, s_ζ)) ≤ j10ⁿc₁^{−1}σ_H(B̄(θ, 2t) ∖ F_j). So μ(S(H) ∩ B(θ, t)) ≤ j10ⁿc₁^{−1}σ_H(B̄(θ, 2t) ∖ F_j) for θ ∈ F_j and 0 < t < 1/(10j).
 (iv) Density points. By the Lebesgue–Besicovitch density theorem for the finite Borel measure σ_H on E (Mathlib Besicovitch.ae_tendsto_measure_inter_div with s := F_j), for σ_H-a.e. θ ∈ F_j the ratio q(ρ) := σ_H(F_j ∩ B̄(θ, ρ))/σ_H(B̄(θ, ρ)) tends to 1 as ρ ↓ 0. Fix such θ ∈ F_j ⊆ S(H). For 0 < ρ ≤ 1, step 0 gives 0 < σ_H(B̄(θ, ρ)) ≤ 2ⁿC₁ρⁿ. As σ_H is finite and F_j is Borel, σ_H(B̄(θ, ρ) ∖ F_j) = σ_H(B̄(θ, ρ)) − σ_H(F_j ∩ B̄(θ, ρ)) = σ_H(B̄(θ, ρ))(1 − q(ρ)) ≤ 2ⁿC₁ρⁿ(1 − q(ρ)). Combine with (iii) and ρ := 2t: for 0 < t < min(1/(10j), 1/2), t^{−n}μ(S(H) ∩ B(θ, t)) ≤ j10ⁿc₁^{−1}2ⁿC₁2ⁿ(1 − q(2t)), which tends to 0 as t ↓ 0. Hence for every c > 0 there is η > 0 with μ(S(H) ∩ B(θ, t)) ≤ ctⁿ for t ∈ (0, η), i.e. (α) holds at θ.
 By (ii)–(iv), {θ ∈ F : neither (α) nor (β)} ⊆ ⋃_{j≥1}{θ ∈ F_j : (α) fails}, a countable union of σ_H-null sets, which proves the claim.

5. Conclusion. F := S(H) ∖ C is Borel (S(H) closed, C Borel), and μ(F) = 0 by step 2. By step 4, N₁ := {θ ∈ F : neither (α) nor (β) holds at θ} is σ_H-null. As N₁ ⊆ S(H), this means Hⁿ(N₁) = σ_H(N₁) = 0. Let θ ∈ S(H) be not good. Then θ ∉ C, since Ax′(θ) fails; so θ ∈ F. Moreover, by step 3, (α) and (β) both fail at θ, because Ψ0(θ) and Ψ∞(θ) fail. So {θ ∈ S(H) : θ not good} ⊆ N₁, and therefore μHE[n]{θ | θ ∈ H ∧ |θ| = 1 ∧ ¬(Ψ0(θ) ∨ Ψ∞(θ) ∨ Ax′(θ))} = 0. ∎

## Key steps

1. σ_H := Hⁿ⌞S(H) is finite, with cap bounds c₁ρⁿ ≤ σ_H(B(ζ, ρ)) ≤ C₁ρⁿ from bf_sphereCap_measure_bounds.
2. μ(E′) := sup_{0<r<δ} r^{−n}Hⁿ(A ∩ B(a, r) ∩ Λ(E′)), where Λ(E′) is the double cone over E′ ⊆ S(H), is a countably subadditive outer measure on S(H).
3. The axis set C of directions satisfying Ax′ is σ-compact, and μ(S(H) ∖ C) = 0.
4. Caps and slab cones are comparable: Z_θ(s) ⊆ Λ(S(H) ∩ B(θ, 2s)) and Λ(S(H) ∩ B(θ, t)) ⊆ Z_θ(t). So vanishing μ-density of caps gives Ψ0, and infinite upper μ-density gives Ψ∞.
5. Density dichotomy: for a Borel μ-null F ⊆ S(H), at σ_H-a.e. θ ∈ F either μ(caps) = o(tⁿ) or limsup μ(caps)/tⁿ = ∞. The proof uses inner regularity, the closed sets F_j, a Vitali 5r-covering and the Besicovitch density theorem for σ_H.
6. Apply the dichotomy to F := S(H) ∖ C: every non-good θ lies in a σ_H-null set, hence in an Hⁿ-null set.

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
