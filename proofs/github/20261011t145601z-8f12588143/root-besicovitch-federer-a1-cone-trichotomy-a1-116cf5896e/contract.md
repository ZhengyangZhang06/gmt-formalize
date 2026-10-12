<!-- theorem-id: gmt-ch03/root.besicovitch_federer-a1.cone_trichotomy-a1 -->

## Theorem `Submission.bf_coneTrichotomy_ae_frames`

Let n ≥ 1, ℓ ≥ 1, N := n + ℓ, A ⊆ ℝ^N compact with Hⁿ(A) < ∞ and δ > 0. For a linear map p : ℝ^N → ℝ^N and a ∈ ℝ^N let X_p(a, r, s) := {x : |p(x − a)| < s|x − a|} ∩ B(a, r), and say that T(a, p) holds if (Φ0) for every c > 0 there is ε > 0 with Hⁿ(A ∩ X_p(a, r, s)) ≤ c(rs)ⁿ for all 0 < s < ε, 0 < r < δ; or (Φ∞) for every K ∈ ℝ and ε > 0 there are 0 < s < ε, 0 < r < δ with K(rs)ⁿ ≤ Hⁿ(A ∩ X_p(a, r, s)); or (Ax) some b ∈ A has b ≠ a, |b − a| < δ and p(b − a) = 0. Then for Lebesgue-a.e. v ∈ (ℝ^N)ⁿ, if v is linearly independent, Hⁿ({a ∈ A : not T(a, frameProjection v)}) = 0, where frameProjection v is the orthogonal projection onto span v; i.e. ForAlmostAllProjections N n (fun p ↦ Hⁿ{a ∈ A : ¬T(a, p)} = 0).

Node: `root.besicovitch_federer-a1.cone_trichotomy-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/29

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/535, https://github.com/ZhengyangZhang06/gmt-formalize/issues/538, https://github.com/ZhengyangZhang06/gmt-formalize/issues/542, https://github.com/ZhengyangZhang06/gmt-formalize/issues/545, https://github.com/ZhengyangZhang06/gmt-formalize/issues/548, https://github.com/ZhengyangZhang06/gmt-formalize/issues/550

## Lean problem

Declaration: `Submission.bf_coneTrichotomy_ae_frames`

```lean
∀ (n ℓ : ℕ), 0 < n → 0 < ℓ → ∀ A : Set (Rn (n + ℓ)), IsCompact A → μHE[n] A < ∞ → ∀ δ : ℝ, 0 < δ → ForAlmostAllProjections (n + ℓ) n (fun p ↦ μHE[n] {a | a ∈ A ∧ ¬ ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μHE[n] (A ∩ ({x | ‖p (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖p (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r))) ∨ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ p (b - a) = 0)} = 0)
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

- Parent DAG node: `root.besicovitch_federer-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Steps 8 (8a–8d) and 9 of the parent proof: P. Mattila, Geometry of Sets and Measures in Euclidean Spaces, Ch. 18; M. G. Dall'Alba, The Besicovitch-Federer Projection Theorem (Padova 2020), Lemma 4.15, Theorem 4.16 (on the sphere), Lemmas 5.5–5.6; the transfer from Haar measure on O(N) to Lebesgue-a.e. frames is the parent's adaptation (b). All details are written out. This node is the largest of the decomposition and may itself be split along Steps 1–5 below.

0. Notation, standing facts, reduction.
0.1 n ≥ 1, ℓ ≥ 1, N := n + ℓ, ℝ^d := EuclideanSpace ℝ (Fin d), |·| Euclidean norm, x·y inner product, e_1, …, e_N standard basis, B(x, ρ) and B̄(x, ρ) open and closed balls, Hᵐ := μHE[m]. 𝓛 is the space of linear maps ℝ^N → ℝ^N (= ℝ^N →L[ℝ] ℝ^N with the operator norm; a finite-dimensional normed space with its Borel σ-algebra). For p ∈ 𝓛, a ∈ ℝ^N, r, s > 0: X_p(a, r, s) := {x : |p(x − a)| < s|x − a|} ∩ B(a, r) and m(a, p, r, s) := Hⁿ(A ∩ X_p(a, r, s)). Φ0(a, p), Φ∞(a, p), Ax(a, p) and T(a, p) := Φ0 ∨ Φ∞ ∨ Ax are the three conditions of the statement (for this A and δ):
 Φ0(a, p): ∀c > 0 ∃ε > 0 ∀s ∈ (0, ε) ∀r ∈ (0, δ): m(a, p, r, s) ≤ c(rs)ⁿ;
 Φ∞(a, p): ∀K ∈ ℝ ∀ε > 0 ∃s ∈ (0, ε) ∃r ∈ (0, δ): K(rs)ⁿ ≤ m(a, p, r, s);
 Ax(a, p): ∃b ∈ A with b ≠ a, |b − a| < δ, p(b − a) = 0.
 Let 𝒩 := {(a, p) ∈ ℝ^N × 𝓛 : a ∈ A and not T(a, p)} and 𝒩^p := {a : (a, p) ∈ 𝒩} = {a ∈ A : not T(a, p)}. Let 𝒱 ⊆ (ℝ^N)ⁿ be the open set of linearly independent frames; for v ∈ 𝒱, P_v := frameProjection v is the orthogonal projection onto span v. λ denotes the volume (product Lebesgue) measure on (ℝ^N)ⁿ = (Fin n → ℝ^N).
 Goal: λ({v ∈ 𝒱 : Hⁿ(𝒩^{P_v}) > 0}) = 0. This is exactly ForAlmostAllProjections (n + ℓ) n (fun p ↦ μHE[n] {a | a ∈ A ∧ ¬ T(a, p)} = 0).
0.2 Orthogonal group. O(N) := {g ∈ 𝓛 : gᵀg = I} is a closed and bounded subgroup of the invertible maps, hence a compact metrizable topological group (topology of 𝓛). It carries a Haar probability measure θ_N (a left-invariant Borel probability measure). θ_N is also right invariant: for fixed k ∈ O(N), the measure E ↦ θ_N(Ek), i.e. Measure.map (· * k⁻¹) θ_N, is again a left-invariant (left and right multiplications commute) finite Borel measure on the compact group O(N), so it equals c·θ_N for a constant c by uniqueness of Haar measure up to a scalar (Mathlib MeasureTheory.Measure.isMulInvariant_eq_smul_of_compactSpace, which uses IsMulLeftInvariant and IsFiniteMeasureOnCompacts), and c = 1 by comparing total masses. The same applies to the closed subgroup O′ := {g ∈ O(N) : g e_k = e_k for all k ≥ n + 2} (≅ O(n+1)) with Haar probability θ′. For an n-dimensional subspace W, P_W := W.starProjection; for g ∈ O(N), P_{gW} = g P_W gᵀ. Put W₀ := span{e_1, …, e_n}, V₀ := W₀^⊥ = span{e_{n+1}, …, e_N}, P₀ := P_{W₀}.
0.3 μ_A(S) := Hⁿ(A ∩ S) (S Borel) is a finite Borel measure on ℝ^N (A is compact, hence Borel; Hⁿ(A) < ∞). Hⁿ is invariant under translations and orthogonal maps. For an m-dimensional subspace T ⊆ ℝ^N, Hᵐ(T ∩ B(w, ρ)) = ω_m ρᵐ for w ∈ T and ρ > 0, with ω_m ∈ (0, ∞): T with the induced metric is an m-dimensional inner product space on which μHE[m] is the volume measure (Mathlib Isometry.euclideanHausdorffMeasure_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_ball).
0.4 Translation. For a ∈ ℝ^N let A_a := A − a = {b − a : b ∈ A} (compact, Hⁿ(A_a) = Hⁿ(A)). Since X_p(a, r, s) = a + X_p(0, r, s), m(a, p, r, s) = Hⁿ(A_a ∩ X_p(0, r, s)); and Ax(a, p) holds iff some b′ ∈ A_a has b′ ≠ 0, |b′| < δ, p b′ = 0. Hence T(a, p) for A is the same statement as T(0, p) for the set A_a (below, "T(0, p) for A″" means the three conditions at the point 0 with A″ in place of A).

1. Borel measurability (parent 8a).
1.1 Lemma. Let Ξ be a metrizable space, U ⊆ Ξ × ℝ^N open and ν a finite Borel measure on ℝ^N. Then ξ ↦ ν(U_ξ), U_ξ := {x : (ξ, x) ∈ U} (an open set), is lower semicontinuous on Ξ, hence Borel. Proof: let ξ_k → ξ. If x ∈ U_ξ then (ξ, x) lies in the open set U, so (ξ_k, x) ∈ U for all large k; hence 1_{U_ξ}(x) ≤ liminf_k 1_{U_{ξ_k}}(x) for every x. By Fatou's lemma, ν(U_ξ) ≤ ∫ liminf_k 1_{U_{ξ_k}} dν ≤ liminf_k ν(U_{ξ_k}). In a metrizable space sequential lower semicontinuity is lower semicontinuity, and {ξ : ν(U_ξ) > t} is then open.
1.2 Apply 1.1 with Ξ := ℝ^N × 𝓛 × ℝ × ℝ, ν := μ_A and U := {((a, p, r, s), x) : |p(x − a)| < s|x − a| and |x − a| < r} (open: strict inequalities between continuous functions). Since m(a, p, r, s) = μ_A(U_{(a,p,r,s)}), m is lower semicontinuous, hence Borel, on Ξ.
1.3 Monotonicity and left continuity. For fixed (a, p), m(a, p, r, s) is nondecreasing in r and in s. If r_k ↑ r and s_k ↑ s are increasing sequences with 0 < r_k < r and 0 < s_k < s, then X_p(a, r_k, s_k) increases to X_p(a, r, s) (a point x with |x − a| < r and |p(x − a)| < s|x − a| has |x − a| > 0, hence |x − a| < r_k and |p(x − a)| < s_k|x − a| for large k), so m(a, p, r_k, s_k) ↑ m(a, p, r, s) by continuity from below of μ_A.
1.4 Countable forms. Let ℚ₊ := ℚ ∩ (0, ∞).
 (i) Φ0(a, p) ⟺ ∀c ∈ ℚ₊ ∃ε ∈ ℚ₊ ∀s ∈ ℚ ∩ (0, ε) ∀r ∈ ℚ ∩ (0, δ): m(a, p, r, s) ≤ c(rs)ⁿ. [⇒: replace ε by a rational ε′ ∈ (0, ε]. ⇐: for real c > 0 take a rational c′ ∈ (0, c] and its ε; for real s ∈ (0, ε), r ∈ (0, δ) choose rationals s_k ↑ s, r_k ↑ r as in 1.3; then m(a, p, r, s) = lim_k m(a, p, r_k, s_k) ≤ lim_k c′(r_k s_k)ⁿ = c′(rs)ⁿ ≤ c(rs)ⁿ.]
 (ii) Φ∞(a, p) ⟺ ∀K ∈ ℕ ∀ε ∈ ℚ₊ ∃s ∈ ℚ ∩ (0, ε) ∃r ∈ ℚ ∩ (0, δ): m(a, p, r, s) > K(rs)ⁿ. [⇐: for real K and ε > 0 take a natural K′ ≥ K and a rational ε′ ∈ (0, ε]. ⇒: Φ∞ with K + 1 gives real s ∈ (0, ε), r ∈ (0, δ) with m(a, p, r, s) ≥ (K + 1)(rs)ⁿ > K(rs)ⁿ; for rationals s_k ↑ s, r_k ↑ r as in 1.3, m(a, p, r_k, s_k) → m(a, p, r, s) and K(r_k s_k)ⁿ → K(rs)ⁿ, so m(a, p, r_k, s_k) > K(r_k s_k)ⁿ for large k.]
 (iii) {(a, p) : Ax(a, p)} = ⋃_{j ≥ 1, R ∈ ℕ} π(C_{j,R}) with C_{j,R} := {(a, p, b) ∈ ℝ^N × 𝓛 × ℝ^N : |a| ≤ R, ‖p‖ ≤ R, b ∈ A, 1/j ≤ |b − a| ≤ δ − 1/j, p(b − a) = 0} and π(a, p, b) := (a, p). Each C_{j,R} is closed and bounded, hence compact, so π(C_{j,R}) is compact; this set is σ-compact, hence Borel.
 By (i) and (ii), {Φ0} and {Φ∞} are countable Boolean combinations of the Borel sets {(a, p) : m(a, p, r, s) ≤ c(rs)ⁿ} and {(a, p) : m(a, p, r, s) > K(rs)ⁿ} (r, s, c rational, K natural, fixed); with (iii), 𝒩 = (A × 𝓛) ∖ ({Φ0} ∪ {Φ∞} ∪ {Ax}) is a Borel subset of ℝ^N × 𝓛.
1.5 Consequences. (a) p ↦ Hⁿ(𝒩^p) = μ_A(𝒩^p) is Borel on 𝓛 (measurability part of Tonelli's theorem for the finite measure μ_A and the Borel set 𝒩; Mathlib measurable_measure_prodMk_right). Hence 𝒢 := {p ∈ 𝓛 : Hⁿ(𝒩^p) > 0} is Borel. (b) v ↦ P_v is continuous on 𝒱: if M_v is the N×n matrix with columns v_1, …, v_n, then P_v = M_v(M_vᵀM_v)⁻¹M_vᵀ (a self-adjoint idempotent with range span v), and inversion is continuous on invertible matrices. Hence 𝒮 := {v ∈ 𝒱 : P_v ∈ 𝒢} is Borel. (c) g ↦ gP₀gᵀ is continuous on O(N); hence 𝒩′ := {(a, g) ∈ ℝ^N × O(N) : (a, gP₀gᵀ) ∈ 𝒩} and 𝒢̃ := {g ∈ O(N) : gP₀gᵀ ∈ 𝒢} are Borel.

2. Sphere lemma (parent 8b; Dall'Alba Lemma 4.15 and Theorem 4.16 on the sphere).
2.0 Setting. Let H ⊆ ℝ^N be an (n+1)-dimensional subspace with orthogonal projection p_H, S(H) := {θ ∈ H : |θ| = 1}, and σ_H(E) := Hⁿ(E ∩ S(H)) for Borel E (a finite Borel measure by 2.1(c)). Let A′ ⊆ ℝ^N be compact with Hⁿ(A′) < ∞. For θ ∈ S(H) and s > 0 put Z_θ(s) := {x : |p_Hx − (p_Hx·θ)θ| < s|p_Hx|} (the slab cone with axis ℝθ ⊕ H^⊥; |y − (y·θ)θ| = dist(y, ℝθ); p_Hx ≠ 0 on Z_θ(s)), m′(θ, r, s) := Hⁿ(A′ ∩ B(0, r) ∩ Z_θ(s)), and
 Ψ0(θ): ∀c > 0 ∃ε > 0 ∀s ∈ (0, ε) ∀r ∈ (0, δ): m′(θ, r, s) ≤ c(rs)ⁿ;
 Ψ∞(θ): ∀K ∈ ℝ ∀ε > 0 ∃s ∈ (0, ε) ∃r ∈ (0, δ): K(rs)ⁿ ≤ m′(θ, r, s);
 Ax′(θ): ∃x ∈ A′ with x ≠ 0, |x| < δ and p_Hx ∈ ℝθ.
 Call θ good for (H, A′, δ) if Ψ0(θ) ∨ Ψ∞(θ) ∨ Ax′(θ).
 Sphere lemma: the set of θ ∈ S(H) that are not good is contained in a σ_H-null Borel set.
2.1 Sphere estimates. Fix ζ ∈ S(H); let T_ζ := H ∩ ζ^⊥ (n-dimensional) with orthogonal projection π_ζ (1-Lipschitz, π_ζζ = 0), and Γ(w) := w + (1 − |w|²)^{1/2}ζ for w ∈ T_ζ with |w| ≤ 1. Γ maps the closed unit ball of T_ζ bijectively onto {ξ ∈ S(H) : ξ·ζ ≥ 0}, with inverse π_ζ.
 (a) σ_H(B(ζ, ρ)) ≥ ω_n(ρ/2)ⁿ for 0 < ρ ≤ 2. If w ∈ T_ζ and |w| < ρ/2 (≤ 1), then, since 1 − (1 − t)^{1/2} ≤ t for t ∈ [0, 1], |Γ(w) − ζ|² = |w|² + (1 − (1 − |w|²)^{1/2})² ≤ |w|² + |w|⁴ ≤ 2|w|² < ρ². So T_ζ ∩ B(0, ρ/2) ⊆ π_ζ(S(H) ∩ B(ζ, ρ)), and as π_ζ is 1-Lipschitz, Hⁿ(S(H) ∩ B(ζ, ρ)) ≥ Hⁿ(T_ζ ∩ B(0, ρ/2)) = ω_n(ρ/2)ⁿ (0.3).
 (b) σ_H(B(ζ, ρ)) ≤ 2ⁿω_nρⁿ for 0 < ρ ≤ 1/2. If ξ ∈ S(H) ∩ B(ζ, ρ), then ξ·ζ = 1 − |ξ − ζ|²/2 > 0, so ξ = Γ(π_ζξ) with |π_ζξ| = |π_ζ(ξ − ζ)| < ρ. On {w ∈ T_ζ : |w| ≤ 1/2} the function w ↦ (1 − |w|²)^{1/2} has gradient of norm |w|(1 − |w|²)^{−1/2} ≤ 1/√3 < 1, so it is 1-Lipschitz there (convex domain) and Γ is 2-Lipschitz there. Hence Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ 2ⁿHⁿ(T_ζ ∩ B(0, ρ)) = 2ⁿω_nρⁿ.
 (c) S(H) is compact, so finitely many balls B(ζ_i, 1/2) with ζ_i ∈ S(H) cover it, and Hⁿ(S(H)) < ∞ by (b); by (a), Hⁿ(S(H)) ≥ ω_n > 0. For ρ > 1/2, σ_H(B(ζ, ρ)) ≤ Hⁿ(S(H)) ≤ Hⁿ(S(H))(2ρ)ⁿ. Thus σ_H(B(ζ, ρ)) ≤ C₁ρⁿ for all ζ ∈ S(H) and ρ > 0, where C₁ := 2ⁿ max(ω_n, Hⁿ(S(H))); also σ_H(B̄(ζ, ρ)) ≤ σ_H(B(ζ, 2ρ)) ≤ 2ⁿC₁ρⁿ. Put c₁ := 2^{−n}ω_n, so σ_H(B(ζ, ρ)) ≥ c₁ρⁿ for 0 < ρ ≤ 2.
2.2 An outer measure on S(H). For E ⊆ S(H) let Λ(E) := {x ∈ ℝ^N : p_Hx ≠ 0 and (p_Hx/|p_Hx| ∈ E or −p_Hx/|p_Hx| ∈ E)} and μ(E) := sup_{0<r<δ} r^{−n}Hⁿ(A′ ∩ B(0, r) ∩ Λ(E)) ∈ [0, ∞]. Then μ(∅) = 0, μ is monotone, and μ(⋃_i E_i) ≤ Σ_i μ(E_i) for countably many E_i, because Λ(⋃_i E_i) = ⋃_i Λ(E_i), Hⁿ is countably subadditive for each fixed r, and a supremum of countably subadditive monotone set functions is countably subadditive and monotone.
2.3 The axis set. C := {θ ∈ S(H) : Ax′(θ)} = ⋃_{j ≥ 1} π₁(K_j) with K_j := {(θ, x) ∈ S(H) × A′ : 1/j ≤ |x| ≤ δ − 1/j, p_Hx − (p_Hx·θ)θ = 0} (closed in the compact S(H) × A′, hence compact), so C is σ-compact and Borel. Moreover μ(S(H) ∖ C) = 0: if E ⊆ S(H) ∖ C, r ∈ (0, δ) and x ∈ A′ ∩ B(0, r) ∩ Λ(E), then x ≠ 0 (as p_Hx ≠ 0), |x| < δ, and p_Hx ∈ ℝθ for the point θ := ±p_Hx/|p_Hx| ∈ E; so θ ∈ C, contradicting E ∩ C = ∅. Hence A′ ∩ B(0, r) ∩ Λ(E) = ∅ for all r ∈ (0, δ), and μ(E) = 0.
2.4 Caps versus slab cones. For unit vectors ξ, θ: dist(ξ, ℝθ) ≤ |ξ − θ|, and if ξ·θ ≥ 0 then |ξ − θ|² = 2(1 − ξ·θ) ≤ 2(1 − (ξ·θ)²) = 2dist(ξ, ℝθ)², so |ξ − θ| ≤ 2dist(ξ, ℝθ). Consequently, for θ ∈ S(H) and s, t > 0: Z_θ(s) ⊆ Λ(S(H) ∩ B(θ, 2s)) [for x ∈ Z_θ(s), y := p_Hx ≠ 0, the point ξ := ±y/|y| with ξ·θ ≥ 0 satisfies |ξ − θ| ≤ 2dist(ξ, ℝθ) = 2dist(y, ℝθ)/|y| < 2s], and Λ(S(H) ∩ B(θ, t)) ⊆ Z_θ(t) [if ξ := ±y/|y| ∈ B(θ, t) then dist(y, ℝθ)/|y| = dist(ξ, ℝθ) ≤ |ξ − θ| < t]. Also, by definition of μ, Hⁿ(A′ ∩ B(0, r) ∩ Λ(E)) ≤ rⁿμ(E) for r ∈ (0, δ). Therefore:
 (α) If ∀c > 0 ∃η > 0 ∀t ∈ (0, η): μ(S(H) ∩ B(θ, t)) ≤ ctⁿ, then Ψ0(θ). Given c > 0, take η for c2^{−n} and ε := η/2; for s ∈ (0, ε), r ∈ (0, δ): m′(θ, r, s) ≤ Hⁿ(A′ ∩ B(0, r) ∩ Λ(S(H) ∩ B(θ, 2s))) ≤ rⁿμ(S(H) ∩ B(θ, 2s)) ≤ rⁿc2^{−n}(2s)ⁿ = c(rs)ⁿ.
 (β) If ∀K ∀η > 0 ∃t ∈ (0, η): μ(S(H) ∩ B(θ, t)) > Ktⁿ, then Ψ∞(θ). Given K and ε > 0 (if K ≤ 0, any s ∈ (0, ε), r ∈ (0, δ) works), take t ∈ (0, ε) with μ(S(H) ∩ B(θ, t)) > Ktⁿ; by definition of μ there is r ∈ (0, δ) with Hⁿ(A′ ∩ B(0, r) ∩ Λ(S(H) ∩ B(θ, t))) > K(rt)ⁿ, so m′(θ, r, t) > K(rt)ⁿ; take s := t.
2.5 Density dichotomy. Let F ⊆ S(H) be Borel with μ(F) = 0. Then for σ_H-a.e. θ ∈ F the hypothesis of (α) or the hypothesis of (β) holds.
 (i) Reduction to closed F. σ_H is a finite Borel measure on the metric space ℝ^N, hence inner regular by closed sets: there are closed sets F̃_k ⊆ F (k ∈ ℕ) with σ_H(F ∖ ⋃_k F̃_k) = 0, and μ(F̃_k) ≤ μ(F) = 0. As (α), (β) are properties of θ alone, it suffices to prove the claim for each F̃_k. From now on, F denotes a closed subset of S(H) with μ(F) = 0.
 (ii) For j ≥ 1 let F_j := {θ ∈ F : μ(S(H) ∩ B(θ, t)) ≤ jtⁿ for all t ∈ (0, 1/j)}. F_j is closed: if F_j ∋ θ_i → θ, then θ ∈ F (F closed); for t ∈ (0, 1/j) and τ > 0 with t + τ < 1/j we have B(θ, t) ⊆ B(θ_i, t + τ) for large i, so μ(S(H) ∩ B(θ, t)) ≤ j(t + τ)ⁿ, and τ ↓ 0 gives μ(S(H) ∩ B(θ, t)) ≤ jtⁿ. If the hypothesis of (β) fails at θ ∈ F, there are K and η > 0 with μ(S(H) ∩ B(θ, t)) ≤ Ktⁿ for t ∈ (0, η), so θ ∈ F_j for every j ≥ max(K, 1/η). Hence it suffices to show, for each j, that the hypothesis of (α) holds at σ_H-a.e. θ ∈ F_j.
 (iii) Fix j, θ ∈ F_j and t ∈ (0, 1/(10j)). Since μ(F_j) ≤ μ(F) = 0, μ(S(H) ∩ B(θ, t)) ≤ μ(R) + μ(F_j) = μ(R), where R := S(H) ∩ B(θ, t) ∖ F_j. For ζ ∈ R put s_ζ := dist(ζ, F_j)/2; as F_j is closed and contains θ, 0 < s_ζ ≤ |ζ − θ|/2 < t/2, and B(ζ, s_ζ) ⊆ B(θ, 2t) ∖ F_j. By the Vitali covering lemma (radii ≤ t/2; Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement with τ = 2) and separability, there is a countable R′ ⊆ R such that the balls B(ζ, s_ζ), ζ ∈ R′, are pairwise disjoint and every ζ ∈ R lies in B(ζ′, 5s_ζ′) for some ζ′ ∈ R′ (if B(ζ, s_ζ) meets B(ζ′, s_ζ′) and s_ζ ≤ 2s_ζ′, then |ζ − ζ′| < 3s_ζ′). For ζ ∈ R′, dist(ζ, F_j) = 2s_ζ < 5s_ζ gives φ ∈ F_j with |ζ − φ| < 5s_ζ, so B(ζ, 5s_ζ) ⊆ B(φ, 10s_ζ) with 10s_ζ < 5t < 1/j, hence μ(S(H) ∩ B(ζ, 5s_ζ)) ≤ j(10s_ζ)ⁿ ≤ j10ⁿc₁^{−1}σ_H(B(ζ, s_ζ)) by 2.1(c) (s_ζ < 2). By countable subadditivity of μ, R ⊆ ⋃_{ζ∈R′}(S(H) ∩ B(ζ, 5s_ζ)) and the disjointness of the Borel sets B(ζ, s_ζ) ⊆ B(θ, 2t) ∖ F_j: μ(S(H) ∩ B(θ, t)) ≤ j10ⁿc₁^{−1}σ_H(B(θ, 2t) ∖ F_j).
 (iv) By the Lebesgue–Besicovitch density theorem for the finite Borel measure σ_H on ℝ^N (Mathlib Besicovitch.ae_tendsto_measure_inter_div), for σ_H-a.e. θ ∈ F_j: σ_H(F_j ∩ B̄(θ, ρ))/σ_H(B̄(θ, ρ)) → 1 as ρ ↓ 0. For such θ (θ ∈ S(H), so 0 < σ_H(B̄(θ, ρ)) ≤ 2ⁿC₁ρⁿ for ρ ∈ (0, 2] by 2.1), σ_H(B̄(θ, ρ) ∖ F_j) = σ_H(B̄(θ, ρ))·(1 − σ_H(F_j ∩ B̄(θ, ρ))/σ_H(B̄(θ, ρ))) = o(ρⁿ). With (iii) and B(θ, 2t) ⊆ B̄(θ, 2t), t^{−n}μ(S(H) ∩ B(θ, t)) → 0 as t ↓ 0, which is the hypothesis of (α) at θ.
2.6 Proof of the sphere lemma. F := S(H) ∖ C is Borel with μ(F) = 0 (2.3). By 2.5 there is a σ_H-null set N₀ (which may be taken Borel, by passing to a Borel σ_H-null superset) such that every θ ∈ F ∖ N₀ satisfies the hypothesis of (α) or of (β), hence Ψ0(θ) or Ψ∞(θ) (2.4). Every θ ∈ C satisfies Ax′(θ). So every θ ∈ S(H) ∖ N₀ is good.

3. Slab cones versus cones (parent 8c; Dall'Alba Lemma 5.5, generalized).
 Let W ⊆ ℝ^N be n-dimensional, P := P_W, V := W^⊥ with an orthonormal basis u_1, …, u_ℓ, H_j := W ⊕ ℝu_j ((n+1)-dimensional, u_j ∈ S(H_j)), and let A″ ⊆ ℝ^N be any set. Claim: if u_j is good for (H_j, A″, δ) for every j ∈ {1, …, ℓ} (with A″ in place of A′ in 2.0), then T(0, P) holds for A″.
3.1 Formulas. p_{H_j}x = Px + (x·u_j)u_j, so p_{H_j}x − (p_{H_j}x·u_j)u_j = Px and |p_{H_j}x|² = |Px|² + (x·u_j)². Hence, for 0 < s < 1 and κ(s) := s²/(1 − s²), Z_{u_j}(s) (for H_j) = {x : |Px|² < s²(|Px|² + (x·u_j)²)} = {x : |Px|² < κ(s)(x·u_j)²}; since |x|² = |Px|² + Σ_k(x·u_k)², X_P(0, ∞, s) := {x : |Px| < s|x|} = {x : |Px|² < κ(s)Σ_k(x·u_k)²}. Also p_{H_j}x ∈ ℝu_j ⟺ Px = 0.
3.2 Inclusions (0 < s < 1). (a) Z_{u_j}(s) ⊆ X_P(0, ∞, s), as (x·u_j)² ≤ Σ_k(x·u_k)². (b) Let s* := (ℓs²/(1 − s² + ℓs²))^{1/2} ∈ (0, 1); then κ(s*) = ℓκ(s) and s* ≤ √ℓ·s (as ℓ/(1 + (ℓ − 1)s²) ≤ ℓ). For x ∈ X_P(0, ∞, s) choose j with (x·u_j)² ≥ ℓ^{−1}Σ_k(x·u_k)²; then |Px|² < κ(s)Σ_k(x·u_k)² ≤ ℓκ(s)(x·u_j)² = κ(s*)(x·u_j)². So X_P(0, ∞, s) ⊆ ⋃_j Z_{u_j}(s*).
3.3 Proof of the claim. Write m′_j(r, s) := Hⁿ(A″ ∩ B(0, r) ∩ Z_{u_j}(s)); note X_P(0, r, s) = X_P(0, ∞, s) ∩ B(0, r).
 – If Ax′ holds for some j, there is x ∈ A″ with x ≠ 0, |x| < δ and p_{H_j}x ∈ ℝu_j, i.e. Px = 0: this is Ax(0, P) for A″.
 – Otherwise, if Ψ∞ holds for some j: given K and ε > 0, apply Ψ∞ with K and min(ε, 1/2) to get s ∈ (0, min(ε, 1/2)) and r ∈ (0, δ) with K(rs)ⁿ ≤ m′_j(r, s) ≤ Hⁿ(A″ ∩ X_P(0, r, s)) by 3.2(a): this is Φ∞(0, P) for A″.
 – Otherwise Ψ0 holds for every j (each u_j is good). Given c > 0 let c′ := cℓ^{−1}ℓ^{−n/2} and let ε_j be the ε given by Ψ0 for u_j and c′; put ε := min(1/2, min_j ε_j/√ℓ). For s ∈ (0, ε) and r ∈ (0, δ): s* ≤ √ℓ·s < ε_j and s* ∈ (0, 1), so by 3.2(b) and subadditivity, Hⁿ(A″ ∩ X_P(0, r, s)) ≤ Σ_j m′_j(r, s*) ≤ ℓc′(rs*)ⁿ ≤ ℓc′ℓ^{n/2}(rs)ⁿ = c(rs)ⁿ: this is Φ0(0, P) for A″.

4. Averaging over O(N) (parent 8d; Dall'Alba, proof of Lemma 5.6).
4.1 Fix a ∈ A and put A′ := A_a (0.4; compact, Hⁿ(A′) < ∞). For g ∈ O(N): gW₀ is n-dimensional with P_{gW₀} = gP₀gᵀ, (gW₀)^⊥ = gV₀ has the orthonormal basis u_j := ge_{n+j}, and gW₀ ⊕ ℝge_{n+j} = gH⁰_j with H⁰_j := span{e_1, …, e_n, e_{n+j}}. By 3 (with W := gW₀, A″ := A′) and 0.4: if ge_{n+j} is good for (gH⁰_j, A′, δ) for every j, then T(a, gP₀gᵀ) holds. Hence {g : not T(a, gP₀gᵀ)} ⊆ ⋃_{j=1}^{ℓ} B_j with B_j := {g ∈ O(N) : ge_{n+j} is not good for (gH⁰_j, A′, δ)}.
4.2 Measurability of B_1 (as in Step 1). Put H⁰ := H⁰_1. For g ∈ O(N), p_{gH⁰} = g p_{H⁰} gᵀ and q_g(x) := p_{gH⁰}x − (p_{gH⁰}x·ge_{n+1})ge_{n+1} depend continuously on (g, x). By Lemma 1.1 (Ξ := O(N) × ℝ × ℝ, ν := Hⁿ(A′ ∩ ·), U := {((g, r, s), x) : |x| < r and |q_g(x)| < s|p_{gH⁰}x|}), (g, r, s) ↦ Hⁿ(A′ ∩ B(0, r) ∩ Z_{ge_{n+1}}(s)) (slab cone for gH⁰) is lower semicontinuous; it is monotone and left continuous in r and in s exactly as in 1.3 (a point of Z_θ(s) ∩ B(0, r) lies in Z_θ(s′) ∩ B(0, r′) for s′ < s, r′ < r close enough). As in 1.4(i)–(ii), Ψ0 and Ψ∞ at ge_{n+1} for gH⁰ are countable Boolean combinations of Borel conditions on g, and the axis condition is the projection to O(N) of the σ-compact set ⋃_{j≥1}{(g, x) ∈ O(N) × A′ : 1/j ≤ |x| ≤ δ − 1/j, q_g(x) = 0}. Hence B_1 is Borel; let χ := 1_{B_1}.
4.3 Reduction to j = 1. Let σ_j ∈ O(N) be the permutation matrix exchanging e_{n+1} and e_{n+j} (σ_1 := I). Then σ_jH⁰_1 = H⁰_j and σ_je_{n+1} = e_{n+j}, so g ∈ B_j ⟺ gσ_j ∈ B_1, i.e. B_j = B_1σ_j^{−1}, which is Borel with θ_N(B_j) = θ_N(B_1) by right invariance.
4.4 The law of g′e_{n+1}. Let S⁰ := S(H⁰) and let ν₀ be the image of θ′ under g′ ↦ g′e_{n+1} ∈ S⁰. Every g′ ∈ O′ fixes span{e_{n+2}, …, e_N} pointwise, hence maps its orthogonal complement H⁰ onto itself and S⁰ onto itself isometrically. Claim: ν₀ = σ̄ := σ_{H⁰}/Hⁿ(S⁰) (well defined by 2.1(c)); both are regarded as Borel probability measures on ℝ^N concentrated on the compact set S⁰ (equivalently, as measures on the subtype S⁰), and the comparison below takes place in this one space. Both are O′-invariant Borel probability measures on S⁰ (ν₀ by left invariance of θ′; σ̄ because Hⁿ is invariant under isometries). For any O′-invariant Borel probability ν on S⁰ and continuous φ : S⁰ → ℝ: ∫φ dν = ∫_{O′}∫_{S⁰}φ(g′x) dν(x) dθ′(g′) = ∫_{S⁰}Ψ_φ(x) dν(x) with Ψ_φ(x) := ∫_{O′}φ(g′x) dθ′(g′) (invariance, then Fubini for the bounded continuous (g′, x) ↦ φ(g′x)). Ψ_φ is constant on S⁰: for x, y ∈ S⁰ there is k ∈ O′ with x = ky (O′ acts transitively on S⁰: e.g. the reflection of H⁰ exchanging x and y, extended by the identity on (H⁰)^⊥), and Ψ_φ(ky) = ∫φ(g′ky) dθ′(g′) = Ψ_φ(y) by right invariance of θ′. Hence ∫φ dν = Ψ_φ(e_{n+1}) is the same for every such ν. Two finite Borel measures on the compact metric space S⁰ with equal integrals of all continuous functions are equal; so ν₀ = σ̄.
4.5 Fibres over cosets. Let h ∈ O(N) and g′ ∈ O′. Then hg′H⁰ = hH⁰, and for θ ∈ S⁰: hθ is good for (hH⁰, A′, δ) iff θ is good for (H⁰, h^{−1}A′, δ). Indeed p_{hH⁰} = hp_{H⁰}hᵀ, so the slab cone of (hH⁰, hθ) with parameter s is h·Z_θ(s) (slab cone of (H⁰, θ)); B(0, r) = hB(0, r); Hⁿ(A′ ∩ h(B(0, r) ∩ Z_θ(s))) = Hⁿ(h^{−1}A′ ∩ B(0, r) ∩ Z_θ(s)) (Hⁿ is invariant under h^{−1}); and x ∈ A′, x ≠ 0, |x| < δ, p_{hH⁰}x ∈ ℝhθ iff y := h^{−1}x ∈ h^{−1}A′, y ≠ 0, |y| < δ, p_{H⁰}y ∈ ℝθ. The set h^{−1}A′ is compact with Hⁿ(h^{−1}A′) = Hⁿ(A′) < ∞, so the sphere lemma (Step 2, applied to H⁰ and h^{−1}A′) gives a σ_{H⁰}-null Borel set N_h ⊆ ℝ^N containing every θ ∈ S⁰ that is not good for (H⁰, h^{−1}A′, δ). By 4.4: ∫_{O′}χ(hg′) dθ′(g′) = θ′({g′ : g′e_{n+1} is not good for (H⁰, h^{−1}A′, δ)}) ≤ θ′({g′ : g′e_{n+1} ∈ N_h}) = ν₀(N_h) = σ̄(N_h) = 0.
4.6 Fubini. (h, g′) ↦ χ(hg′) is Borel on O(N) × O′. By right invariance, ∫_{O(N)}χ(h) dθ_N(h) = ∫_{O(N)}χ(hg′) dθ_N(h) for each g′ ∈ O′. Integrating over g′ (θ′ is a probability) and using Tonelli: ∫χ dθ_N = ∫_{O′}∫_{O(N)}χ(hg′) dθ_N(h) dθ′(g′) = ∫_{O(N)}∫_{O′}χ(hg′) dθ′(g′) dθ_N(h) = 0 by 4.5. So θ_N(B_1) = 0, hence θ_N(B_j) = 0 for all j (4.3) and θ_N({g : not T(a, gP₀gᵀ)}) = 0 (4.1). This holds for every a ∈ A.
4.7 Tonelli over A × O(N). The set 𝒩′ of 1.5(c) is Borel; its section at a is {g : not T(a, gP₀gᵀ)} if a ∈ A and ∅ otherwise. By Tonelli for the finite measures μ_A and θ_N: ∫_{O(N)}μ_A({a : (a, g) ∈ 𝒩′}) dθ_N(g) = ∫_{ℝ^N}θ_N({g : (a, g) ∈ 𝒩′}) dμ_A(a) = 0 by 4.6, and {a : (a, g) ∈ 𝒩′} = 𝒩^{gP₀gᵀ}. Hence Hⁿ(𝒩^{gP₀gᵀ}) = 0 for θ_N-a.e. g, i.e. θ_N(𝒢̃) = 0 (𝒢̃ as in 1.5(c)).

5. Transfer to Lebesgue-a.e. frames (parent 9) and conclusion.
5.1 For g ∈ O(N) and v ∈ (ℝ^N)ⁿ put g·v := (gv_1, …, gv_n). The map (g, v) ↦ g·v is continuous, and λ is invariant under v ↦ g·v: each factor's volume on EuclideanSpace ℝ (Fin N) is invariant under the linear isometry g (|det g| = 1), hence so is the product measure. If v ∈ 𝒱 then g·v ∈ 𝒱, span(g·v) = g·span(v), and P_{g·v} = gP_vgᵀ; if v ∉ 𝒱 then g·v ∉ 𝒱.
5.2 For v ∈ 𝒱 choose h ∈ O(N) with hW₀ = span v (send e_1, …, e_n to an orthonormal basis of span v and e_{n+1}, …, e_N to one of its orthogonal complement); then P_v = hP₀hᵀ and P_{g·v} = (gh)P₀(gh)ᵀ. Hence {g : g·v ∈ 𝒮} = {g : gh ∈ 𝒢̃} = 𝒢̃h^{−1}, and θ_N({g : g·v ∈ 𝒮}) = θ_N(𝒢̃) = 0 by right invariance and 4.7. For v ∉ 𝒱 this set is empty because 𝒮 ⊆ 𝒱.
5.3 The set {(g, v) : g·v ∈ 𝒮} ⊆ O(N) × (ℝ^N)ⁿ is Borel (1.5(b), 5.1). Using invariance (λ({v : g·v ∈ 𝒮}) = λ(𝒮) for every g), θ_N(O(N)) = 1, Tonelli (θ_N finite, λ σ-finite) and 5.2:
 λ(𝒮) = ∫_{O(N)}λ({v : g·v ∈ 𝒮}) dθ_N(g) = ∫_{(ℝ^N)ⁿ}θ_N({g : g·v ∈ 𝒮}) dλ(v) = 0.
5.4 Conclusion. 𝒮 = {v ∈ 𝒱 : Hⁿ({a ∈ A : not T(a, P_v)}) > 0} is λ-null. Hence for λ-a.e. v ∈ (ℝ^N)ⁿ: if v is linearly independent, then μHE[n] {a | a ∈ A ∧ ¬ T(a, frameProjection v)} = 0, where T(a, p) is precisely the disjunction Φ0 ∨ Φ∞ ∨ Ax written in the Lean statement (cone {x | ‖p (x − a)‖ < s * ‖x − a‖} ∩ Metric.ball a r, bounds ENNReal.ofReal (c * (r * s) ^ n) and ENNReal.ofReal (K * (r * s) ^ n), axis condition ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ p (b − a) = 0). This is ForAlmostAllProjections (n + ℓ) n (fun p ↦ μHE[n] {a | a ∈ A ∧ ¬ T(a, p)} = 0). ∎

## Key steps

1. Measurability: cone masses are lower semicontinuous in (a, p, r, s) (Fatou), monotone and left continuous, so Φ0, Φ∞ have rational forms; the axis condition is σ-compact; the exceptional set 𝒩 ⊆ ℝ^N × 𝓛 is Borel.
2. Sphere lemma: for an (n+1)-plane H the outer measure μ(E) = sup_r r^{−n}Hⁿ(A′ ∩ B(0,r) ∩ Λ(E)) vanishes off the σ-compact axis set; a density dichotomy for μ on S(H) (closed F_j, 5r-covering, sphere estimates, Besicovitch density) and the cap/slab-cone comparison give goodness for Hⁿ-a.e. θ ∈ S(H).
3. Slab cones versus cones: Z_{u_j}(s) ⊆ X(0, V, s) ⊆ ⋃_j Z_{u_j}(s*), s* ≤ √ℓ s; if all ℓ slab directions u_j are good then the trichotomy T holds.
4. Haar averaging over O(N): reduce to j = 1 by a permutation; the law of g′e_{n+1} under the Haar measure of O′ ≅ O(n+1) is normalized Hⁿ on the sphere (uniqueness of invariant probabilities); coset invariance, the sphere lemma and Fubini with right invariance give θ_N-null bad sets; Tonelli over A × O(N).
5. Transfer: Lebesgue measure on frames is O(N)-invariant; Tonelli and right invariance turn the θ_N-null set of bad planes into a Lebesgue-null set of frames.

## Reference use

### local-project

Queries:
- `cat manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n "^def ForAlmostAllProjections|^noncomputable def frameProjection|^def BesicovitchFedererProjectionTheorem" project/GMT/Ch03/Contract.lean`
- `rg -n "theorem measurable_rectifiable_purelyUnrectifiable_decomposition|theorem PurelyUnrectifiable.mono|theorem countablyRectifiable_iUnion" simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n "theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement|theorem exists_disjoint_covering_ae" mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n "theorem _root_.Monotone.measure_iUnion" mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `rg -n "theorem LipschitzOnWith.extend_real|theorem LipschitzOnWith.extend_pi" mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `rg -n "theorem ae_tendsto_measure_inter_div" mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n "instance instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace" mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `rg -n "InnerProductSpace.euclideanHausdorffMeasure_eq_volume|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_zero" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "theorem hausdorffMeasure_zero_singleton" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n "theorem starProjection_norm_le" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n "theorem finrank_span_eq_card" mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `rg -n "lemma isMulInvariant_eq_smul_of_compactSpace" mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `rg -n "IsTopologicalGroup \(unitary R\)" mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `rg -l -i "besicovitch.?federer|purely.?unrectifiable" mathlib/Mathlib`
- `rg -l -i "CompactSpace \(Matrix.orthogonalGroup|orthogonalGroup.*CompactSpace" mathlib/Mathlib`
- `rg -n -i "orthogonalGroup|haar|grassmann" simongmt/Poincare/SimonGMT (only Ch02 additive-Haar area lemmas and a Ch08 Grassmannian type; no O(N) Haar measure)`
- `lake env lean on comparator-scope test files (import GMT.Ch03.Submission + replayed contract scope) elaborating all 8 child types and three Lean assemblies (parent; compact_case; cone_density_positive)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SymmetricVitali.lean`

Pinned snapshot (project d09bc8a, Mathlib 25730c7c) plus the pinned simongmt package. Reused by the children: SimonGMT measurable_rectifiable_purelyUnrectifiable_decomposition (measurable Lemma 3.2, used by compact_reduction instead of the sibling node, avoiding a cycle), PurelyUnrectifiable.mono, CountablyRectifiable.mono/countablyRectifiable_iUnion, euclideanHausdorffMeasure_image_le_of_lipschitzOn (Lipschitz image bound for μHE); Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement (5r-lemma) and Vitali.exists_disjoint_covering_ae, Monotone.measure_iUnion (continuity from below for arbitrary sets), LipschitzOnWith.extend_real/extend_pi (McShane), Besicovitch.ae_tendsto_measure_inter_div (density theorem for finite measures), InnerRegularCompactLTTop for all measures on Polish spaces, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_zero + hausdorffMeasure_zero_singleton, Submodule.starProjection_norm_le, finrank_span_eq_card, Haar uniqueness on compact groups (isMulInvariant_eq_smul_of_compactSpace), IsTopologicalGroup (unitary R). No match: neither Mathlib nor SimonGMT contains the Besicovitch–Federer theorem, the cone lemmas, a CompactSpace instance or Haar measure for the orthogonal group, or invariant measures on Grassmannians/spheres in Hausdorff normalization; these are supplied by the children's proofs (cone_trichotomy carries the O(N) Haar-averaging argument).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
