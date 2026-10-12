<!-- theorem-id: gmt-ch03/root.besicovitch_federer-a1 -->

## Theorem `Submission.besicovitchFedererProjectionTheorem_holds`

For n, ℓ ∈ ℕ, N := n + ℓ: if Q ⊆ ℝ^N is purely n-unrectifiable (every countably n-rectifiable subset is Hⁿ-null) and Q = ⋃ⱼ Qⱼ with Hⁿ(Qⱼ) < ∞, then ForAlmostAllProjections N n (fun p ↦ Hⁿ(p(Q)) = 0), i.e. for Lebesgue-a.e. v ∈ (ℝ^N)ⁿ with v linearly independent, Hⁿ(p_v(Q)) = 0 where p_v = frameProjection v is the orthogonal projection onto span v.

Node: `root.besicovitch_federer-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/22

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/104, https://github.com/ZhengyangZhang06/gmt-formalize/issues/105, https://github.com/ZhengyangZhang06/gmt-formalize/issues/106, https://github.com/ZhengyangZhang06/gmt-formalize/issues/107, https://github.com/ZhengyangZhang06/gmt-formalize/issues/108, https://github.com/ZhengyangZhang06/gmt-formalize/issues/109, https://github.com/ZhengyangZhang06/gmt-formalize/issues/110, https://github.com/ZhengyangZhang06/gmt-formalize/issues/111

## Lean problem

Declaration: `Submission.besicovitchFedererProjectionTheorem_holds`

```lean
BesicovitchFedererProjectionTheorem
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
- Child DAG node: `root.besicovitch_federer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and departure. Simon, Ch. 3, Theorem 3.6 (chapter-03.txt lines 530-536, printed p. 80) gives no proof: “For the proof of this theorem see [Fed69] or [Ros84]” (line 536). The printed argument is therefore incomplete (absent), and we supply the standard proof of the Besicovitch-Federer projection theorem from P. Mattila, Geometry of Sets and Measures in Euclidean Spaces (CUP 1995), Ch. 15 (cone criteria) and Ch. 18 (Theorem 18.1), in the presentation of M. G. Dall'Alba, The Besicovitch-Federer Projection Theorem (Master's thesis, Padova 2020, https://www.math.unipd.it/~monti/tesi/DallAlba.pdf), Lemmas 4.5-4.7, 4.15-4.16, 5.2-5.6 and the proof of Theorem 5.1; cf. [Fed69, §3.3]. Two adaptations: (a) the reduction from σ-finite, possibly non-measurable Q to compact purely unrectifiable sets (Step 1), using SimonGMT's measurable form of Lemma 3.2 (not the sibling, to avoid a dependency cycle); (b) the contract encodes “σ-a.e. p ∈ O(n+ℓ, n)” as “Lebesgue-a.e. linearly independent frame v ∈ (ℝ^{n+ℓ})ⁿ, p = orthogonal projection onto span v” (ForAlmostAllProjections, frameProjection); Step 9 transfers the Haar-measure statement to frames.

Notation. N := n + ℓ, ℝ^d = EuclideanSpace ℝ (Fin d), Hⁿ = μHE[n], B(a, r) open ball, ω_n = Lⁿ(B(0,1)). For an ℓ-dimensional subspace V (“the fibre direction”), W := V^⊥ (n-dimensional) and Q_V := orthogonal projection onto W (so Q_V = frameProjection v when W = span v). Hⁿ restricted to an n-plane is its Lebesgue measure; Q_V is 1-Lipschitz. Cones: for a ∈ ℝ^N, 0 < s < 1, r > 0,
 X(a, V, s) := {x : |Q_V(x − a)| < s|x − a|} (an open cone around a + V, not containing a), X(a, r, V, s) := X(a, V, s) ∩ B(a, r).
Note Q_V(X(a, r, V, s)) ⊆ W ∩ B(Q_V a, rs). O(N) denotes the orthogonal group (a compact metrizable group) and θ_N its Haar probability measure, which is left and right invariant (compact groups are unimodular).

Statement. If Q ⊆ ℝ^N is purely n-unrectifiable and Q = ⋃ⱼ Qⱼ with Hⁿ(Qⱼ) < ∞, then for Lebesgue-a.e. v ∈ (ℝ^N)ⁿ with v linearly independent, Hⁿ(frameProjection v '' Q) = 0.

Proof.

0. Trivial cases. If n = 0: any x ∈ Q gives the countably 0-rectifiable subset {x} (range of a constant map ℝ⁰ → ℝ^N) with H⁰({x}) = 1 > 0, so Q = ∅ and the claim is trivial. If ℓ = 0: Q ⊆ ℝⁿ = range(id) is countably n-rectifiable, so Hⁿ(Q) = 0 by pure unrectifiability and Hⁿ(p(Q)) ≤ Hⁿ(Q) = 0 for every 1-Lipschitz p. Assume n ≥ 1, ℓ ≥ 1.

1. Reduction to compact sets (adaptation (a)). For each j choose a Borel Bⱼ ⊇ Qⱼ with Hⁿ(Bⱼ) = Hⁿ(Qⱼ) < ∞ (Borel regularity; Mathlib toMeasurable). By the measurable case of Lemma 3.2 (SimonGMT Chapter03.measurable_rectifiable_purelyUnrectifiable_decomposition), Bⱼ = Rⱼ ∪ Pⱼ with Rⱼ Borel and countably n-rectifiable and Pⱼ Hⁿ-measurable and purely n-unrectifiable. Qⱼ ∩ Rⱼ ⊆ Q is countably rectifiable, so Hⁿ(Qⱼ ∩ Rⱼ) = 0 (Q is purely unrectifiable). By inner regularity of the finite Borel regular measure Hⁿ⌞Bⱼ (Simon Ch. 1, 1.15(2), 1.16) Pⱼ contains a countable union of compact sets K_{j,i} with Hⁿ(Pⱼ ∖ ⋃ᵢ K_{j,i}) = 0. Thus Q ⊆ Z ∪ ⋃_{j,i} K_{j,i} with Hⁿ(Z) = 0 and each K_{j,i} compact, purely n-unrectifiable (⊆ Pⱼ) with Hⁿ(K_{j,i}) < ∞. As every Q_V is 1-Lipschitz, Hⁿ(Q_V(Z)) = 0 for every V. A countable intersection of full-measure sets of frames has full measure, so it suffices to prove: for every compact, purely n-unrectifiable A ⊆ ℝ^N with Hⁿ(A) < ∞, Hⁿ(frameProjection v '' A) = 0 for Lebesgue-a.e. linearly independent v. Fix such A for Steps 2-10.

2. Cone-free sets are rectifiable (Mattila 15.13; Dall'Alba Lemma 4.5). Let V, 0 < s < 1, r ∈ (0, ∞] and E ⊆ ℝ^N with E ∩ X(a, r, V, s) = ∅ for all a ∈ E. Then E is countably n-rectifiable. Proof: cover E by countably many sets Eᵢ of diameter < r. For a, b ∈ Eᵢ, |b − a| < r and b ∉ X(a, r, V, s) give |Q_V(b − a)| ≥ s|b − a|; so Q_V|Eᵢ is injective with (1/s)-Lipschitz inverse Q_V(Eᵢ) → Eᵢ. Extend this inverse to a Lipschitz map W → ℝ^N (Simon Ch. 2, 1.2, coordinatewise) and precompose with a linear isometry ℝⁿ → W: Eᵢ is contained in the range of a Lipschitz map ℝⁿ → ℝ^N.

3. Small cone mass forces small mass (Mattila 15.14; Dall'Alba Lemma 4.6, constants adjusted). Let V, 0 < s < 1, δ > 0, λ > 0 and let B ⊆ ℝ^N be purely n-unrectifiable with Hⁿ(B ∩ X(x, r, V, s)) ≤ λ rⁿ sⁿ for all x ∈ B and 0 < r < δ. Then Hⁿ(B ∩ B(a, δ/8)) ≤ 2·15ⁿ λ δⁿ for every a ∈ ℝ^N.
 Proof. Let B' := B ∩ B(a, δ/8) and B'' := {x ∈ B' : B' ∩ X(x, V, s/4) ≠ ∅}. The set E := B' ∖ B'' satisfies E ∩ X(x, V, s/4) = ∅ for x ∈ E, so it is countably rectifiable by Step 2 (r = ∞), hence Hⁿ(E) = 0 (E ⊆ B); so Hⁿ(B') = Hⁿ(B''). For x ∈ B'' let h(x) := sup{|y − x| : y ∈ B' ∩ X(x, V, s/4)} ∈ (0, δ/4] and pick x' ∈ B' ∩ X(x, V, s/4) with |x' − x| ≥ 3h(x)/4. Let C_x := {z : |Q_V(z − x)| < s h(x)/4}. Claim: B' ∩ C_x ⊆ {x} ∪ X(x, 3h(x), V, s) ∪ X(x', 3h(x), V, s). Let z ∈ B' ∩ C_x, z ≠ x. If |z − x| > h(x) then |Q_V(z − x)| < s h(x)/4 < (s/4)|z − x|, i.e. z ∈ B' ∩ X(x, V, s/4), contradicting the definition of h(x); so |z − x| ≤ h(x) and |z − x'| ≤ 2h(x) < 3h(x). If z = x', then z ∈ X(x, 3h(x), V, s) because x' ∈ X(x, V, s/4) ⊆ X(x, V, s) and |x' − x| ≤ h(x). If z ∈ X(x', V, s), then z ∈ X(x', 3h(x), V, s) because |z − x'| < 3h(x). Otherwise z ≠ x' and z ∉ X(x', V, s), i.e. s|z − x'| ≤ |Q_V(z − x')| ≤ |Q_V(z − x)| + |Q_V(x − x')| < s h(x)/4 + (s/4)|x − x'| ≤ s h(x)/2; then |z − x'| < h(x)/2, so |z − x| > 3h(x)/4 − h(x)/2 = h(x)/4 > |Q_V(z − x)|/s, i.e. z ∈ X(x, V, s), and |z − x| ≤ h(x) < 3h(x), so z ∈ X(x, 3h(x), V, s). Since x, x' ∈ B and 3h(x) ≤ 3δ/4 < δ, the hypothesis gives Hⁿ(B' ∩ C_x) ≤ 2λ(3h(x))ⁿsⁿ (n ≥ 1, so {x} is null). The balls W ∩ B(Q_V x, s h(x)/20), x ∈ B'', have bounded radii; by the 5r-covering lemma (Simon Ch. 1, 3.4) there are countably many xᵢ ∈ B'' with these balls pairwise disjoint and Q_V(B'') ⊆ ⋃ᵢ W ∩ B(Q_V xᵢ, s h(xᵢ)/4); hence B'' ⊆ ⋃ᵢ C_{xᵢ}. The disjoint balls lie in W ∩ B(Q_V a, δ/8 + δ/80) ⊆ W ∩ B(Q_V a, δ/4). Therefore Hⁿ(B') ≤ Σᵢ 2λ 3ⁿ sⁿ h(xᵢ)ⁿ = 2λ 60ⁿ ω_n⁻¹ Σᵢ Hⁿ(W ∩ B(Q_V xᵢ, s h(xᵢ)/20)) ≤ 2λ 60ⁿ (δ/4)ⁿ = 2·15ⁿ λ δⁿ. ∎

4. Cone density is positive a.e. (Mattila 15.15-15.16; Dall'Alba Corollary 4.7). For every V and δ > 0, for Hⁿ-a.e. a ∈ A: Φ_δ(a, V) := limsup_{s↓0} sup_{0<r<δ} (rs)^{-n} Hⁿ(A ∩ X(a, r, V, s)) > 0.
 Proof. Let Z be the set where Φ_δ(a, V) = 0. Fix λ > 0 and for i ∈ ℕ let Zᵢ := {a ∈ Z : sup_{0<r<δ}(rs)^{-n}Hⁿ(A ∩ X(a, r, V, s)) ≤ λ for all s ∈ (0, 1/i)}. Then Zᵢ ↑ and ⋃ᵢ Zᵢ = Z. For fixed i and s ∈ (0, 1/i), B := Zᵢ ⊆ A is purely unrectifiable and Hⁿ(B ∩ X(x, r, V, s)) ≤ Hⁿ(A ∩ X(x, r, V, s)) ≤ λ rⁿ sⁿ for x ∈ B, r < δ; Step 3 gives Hⁿ(Zᵢ ∩ B(a, δ/8)) ≤ 2·15ⁿλδⁿ for all a. Letting i → ∞ (continuity from below of the outer measure Hⁿ along increasing sequences, Borel regularity) and then λ ↓ 0: Hⁿ(Z ∩ B(a, δ/8)) = 0 for all a; countably many such balls cover ℝ^N, so Hⁿ(Z) = 0. ∎

5. First exceptional set (Dall'Alba Lemma 5.2). A_{1,δ}(V) := {a ∈ A : Φ_δ(a, V) = 0} has Hⁿ(A_{1,δ}(V)) = 0, by Step 4.

6. Second exceptional set (Dall'Alba Lemma 5.3). A_{2,δ}(V) := {a ∈ A : Φ_δ(a, V) = ∞} has Hⁿ(Q_V(A_{2,δ}(V))) = 0.
 Proof. Fix K > 0. Each a ∈ A_{2,δ}(V) admits arbitrarily small s > 0 and some r ∈ (0, δ) with Hⁿ(A ∩ X(a, r, V, s)) ≥ K(rs)ⁿ; the closed balls W ∩ B̄(Q_V a, rs) (radius rs < δs, arbitrarily small) form a fine cover of Q_V(A_{2,δ}(V)). By the Vitali covering theorem for Lebesgue (outer) measure on the n-plane W (Simon Ch. 1, Remark 3.11 / Symmetric Vitali Property; Mathlib Vitali.exists_disjoint_covering_ae) there are countably many pairwise disjoint such balls W ∩ B̄(Q_V aᵢ, rᵢsᵢ) covering Hⁿ-almost all of Q_V(A_{2,δ}(V)). The sets A ∩ X(aᵢ, rᵢ, V, sᵢ) are Borel and pairwise disjoint (their Q_V-images lie in the disjoint balls), so Hⁿ(Q_V(A_{2,δ}(V))) ≤ Σᵢ ω_n(rᵢsᵢ)ⁿ ≤ (ω_n/K)Σᵢ Hⁿ(A ∩ X(aᵢ, rᵢ, V, sᵢ)) ≤ ω_n Hⁿ(A)/K. Let K → ∞. ∎

7. Third exceptional set (Dall'Alba Lemma 5.4). A₃(V) := {a ∈ A : A ∩ (a + V) is infinite} has Hⁿ(Q_V(A₃(V))) = 0.
 Proof. Let ι : ℝⁿ → W be a linear isometry and f := ι⁻¹∘Q_V : ℝ^N → ℝⁿ (1-Lipschitz). The sibling eilenberg_inequality (with m := n, k := 0) gives a Borel g ≥ H⁰(A ∩ f⁻¹{y}) with ∫ g dLⁿ ≤ C·Hⁿ(A) < ∞, so H⁰(A ∩ f⁻¹{y}) < ∞ for Lⁿ-a.e. y. For a ∈ A₃(V), f⁻¹{f(a)} = a + V, so f(A₃(V)) ⊆ {g = ∞}, an Lⁿ-null set, and Q_V(A₃(V)) = ι(f(A₃(V))) is Hⁿ-null. ∎

8. The key lemma (Mattila Ch. 18; Dall'Alba Lemma 5.6). For δ > 0 and V let A_{3,δ}(V) := {a ∈ A : (A ∖ {a}) ∩ (a + V) ∩ B(a, δ) ≠ ∅}, and say that the trichotomy T_δ(a, V) holds if Φ_δ(a, V) ∈ {0, ∞} or a ∈ A_{3,δ}(V). Claim: for θ_N-a.e. g ∈ O(N), and also (Step 9) for Lebesgue-a.e. frame v, Hⁿ({a ∈ A : not T_δ(a, V)}) = 0, where V = gV₀ (V₀ := span{e_{n+1}, …, e_N}), resp. V = (span v)^⊥.
 8a. Measurability. Parametrize V by the projection Q = Q_V (a continuous function of g, and of v on the open set of independent frames: Q = v(vᵀv)⁻¹vᵀ). The indicator of {(x, a, Q, r, s) : |Q(x − a)| < s|x − a|, |x − a| < r} is lower semicontinuous, so (a, Q, r, s) ↦ Hⁿ(A ∩ X(a, r, V, s)) is lower semicontinuous (Fatou, Hⁿ⌞A finite) hence Borel; it is nondecreasing and left-continuous in r and in s, so the sup over r ∈ (0, δ) and the limsup over s ↓ 0 may be taken along rationals (for rationals s₁ < s < s₂, (rs₂)^{-n}Hⁿ(…s₁) ≤ (rs)^{-n}Hⁿ(…s) ≤ (rs₁)^{-n}Hⁿ(…s₂)), and (a, Q) ↦ Φ_δ(a, V) is Borel. The set {(a, Q) : a ∈ A_{3,δ}(V)} is the projection of the σ-compact set ⋃_j{(a, Q, b) ∈ A × 𝒬 × A : 1/j ≤ |b − a| ≤ δ − 1/j, (I − Q)(b − a) = b − a} (𝒬 the compact set of rank-n orthogonal projections), hence σ-compact. So (a, Q) ↦ T_δ(a, V) is Borel.
 8b. Sphere lemma (Dall'Alba Theorem 4.16 and first part of the proof of 5.6). Let H ⊆ ℝ^N be an (n+1)-dimensional subspace, S(H) its unit sphere (≅ Sⁿ, with the measure Hⁿ⌞S(H)), p_H the orthogonal projection onto H, and for θ ∈ S(H), 0 < s < 1: Z_{H,θ}(s) := {x : dist(p_H x, ℝθ) < s|p_H x|} (“slab cone” with axis ℝθ ⊕ H^⊥). Let A' ⊆ ℝ^N be compact with Hⁿ(A') < ∞ and say (H, θ) is good for A' if Ψ(θ) := limsup_{s↓0} sup_{0<r<δ}(rs)^{-n}Hⁿ(A' ∩ B(0, r) ∩ Z_{H,θ}(s)) ∈ {0, ∞} or (A' ∖ {0}) ∩ B(0, δ) ∩ (ℝθ ⊕ H^⊥) ≠ ∅. Claim: for Hⁿ-a.e. θ ∈ S(H), (H, θ) is good for A'.
 Proof. For E ⊆ S(H) let Λ(E) := {x : p_H x ≠ 0, p_H x/|p_H x| ∈ E or −p_H x/|p_H x| ∈ E} and μ(E) := sup_{0<r<δ} r^{-n}Hⁿ(A' ∩ B(0, r) ∩ Λ(E)); μ is an outer measure on S(H) (Λ(∅) = ∅, Λ commutes with unions, and a supremum of countably subadditive monotone set functions is countably subadditive and monotone). Let C := {θ : (A' ∖ {0}) ∩ B(0, δ) ∩ (ℝθ ⊕ H^⊥) ≠ ∅}, a σ-compact set (projection of ⋃_j{(θ, x) ∈ S(H) × A' : 1/j ≤ |x| ≤ δ − 1/j, p_H x ∈ ℝθ}). If E ⊆ S(H) ∖ C and r < δ then A' ∩ B(0, r) ∩ Λ(E) = ∅: a point x of it has x ≠ 0, |x| < δ and p_H x ∈ ℝθ for θ := ±p_H x/|p_H x| ∈ E, so x ∈ ℝθ ⊕ H^⊥ and θ ∈ C, a contradiction. Hence μ(S(H) ∖ C) = 0. Density dichotomy (Dall'Alba Lemma 4.15 and Theorem 4.16, on the sphere): for every Borel F ⊆ S(H) with μ(F) = 0, for Hⁿ-a.e. θ ∈ F, limsup_{t↓0} t^{-n}μ(S(H) ∩ B(θ, t)) ∈ {0, ∞}. [Proof: by inner regularity assume F closed. For j ∈ ℕ let F_j := {θ ∈ F : μ(S(H) ∩ B(θ, t)) ≤ j tⁿ for 0 < t < 1/j}; F_j is closed (if θ_i → θ, t < 1/j and τ > 0 small, B(θ, t) ⊆ B(θ_i, t + τ) for large i, so μ(B(θ, t)) ≤ j(t + τ)ⁿ), and {θ ∈ F : limsup < ∞} = ⋃_j F_j. Fix j and θ ∈ F_j, t < 1/(10j): since μ(F_j) = 0, μ(B(θ, t)) ≤ μ(B(θ, t) ∖ F_j). For ζ ∈ S(H) ∩ B(θ, t) ∖ F_j let s_ζ := dist(ζ, F_j)/2 ≤ t/2; the balls B(ζ, s_ζ) lie in B(θ, 2t) ∖ F_j; by the 5r-covering lemma pick disjoint B(ζᵢ, sᵢ) with B(θ, t) ∖ F_j ⊆ ⋃ᵢ B(ζᵢ, 5sᵢ); each B(ζᵢ, 5sᵢ) meets F_j at some φᵢ and B(ζᵢ, 5sᵢ) ⊆ B(φᵢ, 10sᵢ) with 10sᵢ < 1/j, so μ(B(ζᵢ, 5sᵢ)) ≤ j 10ⁿ sᵢⁿ ≤ j 10ⁿ c⁻¹ Hⁿ(S(H) ∩ B(ζᵢ, sᵢ)), where c > 0 is such that Hⁿ(S(H) ∩ B(ζ, s)) ≥ c sⁿ for ζ ∈ S(H), s ≤ 2. Summing, μ(B(θ, t)) ≤ C j Hⁿ(S(H) ∩ B(θ, 2t) ∖ F_j), and t^{-n}Hⁿ(S(H) ∩ B(θ, 2t) ∖ F_j) → 0 for Hⁿ-a.e. θ ∈ F_j by the Lebesgue density theorem for the Radon measure Hⁿ⌞S(H) (Besicovitch; Hⁿ(S(H) ∩ B(θ, 2t)) ≤ C' tⁿ).] Apply this with F := S(H) ∖ C. Comparison of caps and slab cones: for unit ξ, θ with ξ·θ ≥ 0, dist(ξ, ℝθ) ≤ |ξ − θ| ≤ 2 dist(ξ, ℝθ); since both Z_{H,θ}(·) and Λ(·) exclude the points with p_H x = 0, this gives Z_{H,θ}(s) ⊆ Λ(S(H) ∩ B(θ, 2s)) and Λ(S(H) ∩ B(θ, t)) ⊆ Z_{H,θ}(t) for every θ ∈ S(H), s, t ∈ (0, 1). Therefore Ψ(θ) ≤ 2ⁿ limsup_t t^{-n}μ(B(θ, t)) and limsup_t t^{-n}μ(B(θ, t)) ≤ Ψ(θ), so the dichotomy for μ gives Ψ(θ) ∈ {0, ∞} for Hⁿ-a.e. θ ∉ C, while every θ ∈ C is good. ∎
 8c. From slab cones to cones (Dall'Alba Lemma 5.5, generalized). Let V be ℓ-dimensional with orthonormal basis u₁, …, u_ℓ, W = V^⊥, H_j := W ⊕ ℝu_j. Then Z_{H_j,u_j}(s) = {x : |Q_V x|² < (s²/(1−s²))(x·u_j)²} and ⋃_j Z_{H_j,u_j}(s) ⊆ X(0, V, s) ⊆ ⋃_j Z_{H_j,u_j}(s*), where s* ∈ (0,1) is defined by s*²/(1 − s*²) = ℓs²/(1 − s²) (so s*/s → √ℓ as s → 0). [x ∈ X(0, V, s) iff |Q_V x|² < (s²/(1−s²))Σ_j(x·u_j)², and some j has (x·u_j)² ≥ ℓ⁻¹Σ_j(x·u_j)².] The axis ℝu_j ⊕ H_j^⊥ equals V. Consequently, if (H_j, u_j) is good for A' (with δ) for every j, then T_δ(0, V) holds for A': if some j has the axis alternative, (A' ∖ {0}) ∩ B(0, δ) ∩ V ≠ ∅; else if some Ψ_j = ∞ then Φ_δ(0, V) = ∞ (Z_{H_j,u_j}(s) ⊆ X(0, V, s)); else all Ψ_j = 0 and (rs)^{-n}Hⁿ(A' ∩ X(0, r, V, s)) ≤ (s*/s)ⁿ Σ_j (rs*)^{-n}Hⁿ(A' ∩ B(0, r) ∩ Z_{H_j,u_j}(s*)) gives Φ_δ(0, V) = 0.
 8d. Averaging over O(N) (Dall'Alba, proof of 5.6, second part). Fix a ∈ A and put A' := A − a (compact); T_δ(a, V) for A is T_δ(0, V) for A'. For g ∈ O(N) use V = gV₀ with basis u_j = g e_{n+j}, so (H_j, u_j) = (gH⁰_j, ge_{n+j}), H⁰_j := span{e₁, …, e_n, e_{n+j}}. By 8c it suffices to show, for each j, θ_N({g : (gH⁰_j, ge_{n+j}) not good for A'}) = 0; composing with a permutation matrix fixing e₁, …, e_n (θ_N is right invariant) we may take j = 1, H⁰ := H⁰_1. Let O' ≅ O(n+1) be the subgroup fixing e_{n+2}, …, e_N, with Haar probability θ'. The image of θ' under g' ↦ g'e_{n+1} is the normalized measure Hⁿ⌞S(H⁰)/Hⁿ(S(H⁰)): both are O'-invariant Borel probabilities on S(H⁰), and for any O'-invariant probability ν and continuous φ, ∫φ dν = ∫∫φ(g'x) dθ'(g') dν(x) = c_φ, because x ↦ ∫φ(g'x)dθ'(g') is constant on S(H⁰) (transitivity of O' and right invariance of θ'); so invariant probabilities are unique. Let χ(g) := 1 if (gH⁰, ge_{n+1}) is not good for A', else 0. χ is Borel by the argument of 8a: {(x, g, r, s) : dist(p_{gH⁰}x, ℝge_{n+1}) < s|p_{gH⁰}x|, |x| < r} is open, so g ↦ Hⁿ(A' ∩ B(0, r) ∩ Z_{gH⁰,ge_{n+1}}(s)) is lower semicontinuous, monotone and left-continuous in r and s (so sup and limsup may be taken along rationals); and the axis condition is the projection of the σ-compact set ⋃_j{(g, x) ∈ O(N) × A' : 1/j ≤ |x| ≤ δ − 1/j, p_{gH⁰}x ∈ ℝge_{n+1}}. For h ∈ O(N), goodness for A' of (hg'H⁰, hg'e_{n+1}) is goodness for h⁻¹A' of (H⁰, g'e_{n+1}) (Hⁿ is invariant under h); by 8b applied to the compact set h⁻¹A' and the uniqueness just proved, ∫_{O'} χ(hg') dθ'(g') = 0 for every h. By right invariance of θ_N and Tonelli, ∫_{O(N)} χ dθ_N = ∫_{O'}∫_{O(N)} χ(hg') dθ_N(h) dθ'(g') = ∫_{O(N)}∫_{O'} χ(hg') dθ'(g') dθ_N(h) = 0. Hence for every a ∈ A, θ_N({g : not T_δ(a, gV₀)}) = 0, and by Tonelli on A × O(N) (Borel by 8a; Hⁿ⌞A finite) θ_N-a.e. g satisfies Hⁿ({a ∈ A : not T_δ(a, gV₀)}) = 0.

9. Transfer to frames (adaptation (b)). Let 𝒢 be a Borel set of ℓ-dimensional subspaces (described through their projections) with θ_N({g : gV₀ ∈ 𝒢}) = 0, and 𝒮 := {v ∈ (ℝ^N)ⁿ linearly independent : (span v)^⊥ ∈ 𝒢} (Borel). Lebesgue measure on (ℝ^N)ⁿ is invariant under v ↦ gv := (gv₁, …, gv_n) for g ∈ O(N). By Tonelli, Leb(𝒮) = ∫_{O(N)} Leb(g⁻¹𝒮) dθ_N(g) = ∫ [∫_{O(N)} 1_𝒮(gv) dθ_N(g)] dv. For fixed independent v choose h ∈ O(N) with hV₀ = (span v)^⊥; then gv ∈ 𝒮 iff ghV₀ ∈ 𝒢, so the inner integral is θ_N({g : ghV₀ ∈ 𝒢}) = θ_N({g' : g'V₀ ∈ 𝒢}h⁻¹) = 0 by right invariance. Hence Leb(𝒮) = 0. Applying this to 𝒢_δ := {V : Hⁿ({a ∈ A : not T_δ(a, V)}) > 0} (Borel in the projection Q_V by 8a and Tonelli) gives: for Lebesgue-a.e. independent v, Hⁿ({a ∈ A : not T_δ(a, (span v)^⊥)}) = 0.

10. Conclusion (Dall'Alba, proof of Theorem 5.1). Let v be independent and outside the null sets of Step 9 for all δ = 1/i, i ≥ 1; V := (span v)^⊥, so Q_V = frameProjection v. Put Gᵢ := {a ∈ A : not T_{1/i}(a, V)} (Hⁿ-null). If a ∈ A lies in none of Gᵢ, A_{1,1/i}(V), A_{2,1/i}(V) (i ≥ 1), then a ∈ A_{3,1/i}(V) for every i, so A ∖ {a} meets a + V in points arbitrarily close to a, hence A ∩ (a + V) is infinite and a ∈ A₃(V). Thus A ⊆ ⋃ᵢ(Gᵢ ∪ A_{1,1/i}(V)) ∪ ⋃ᵢ A_{2,1/i}(V) ∪ A₃(V), and since Q_V is 1-Lipschitz, Hⁿ(Q_V(A)) ≤ Σᵢ Hⁿ(Gᵢ ∪ A_{1,1/i}(V)) + Σᵢ Hⁿ(Q_V(A_{2,1/i}(V))) + Hⁿ(Q_V(A₃(V))) = 0 by Steps 5, 6, 7, 9. With Step 1 this proves ForAlmostAllProjections (n+ℓ) n (fun p ↦ Hⁿ(p '' Q) = 0). ∎

## Key steps

1. Trivial cases n = 0 (Q = ∅) and ℓ = 0 (Hⁿ(Q) = 0).
2. Reduce to compact purely unrectifiable A with Hⁿ(A) < ∞ (Borel hulls, SimonGMT measurable Lemma 3.2, inner regularity).
3. Cone lemmas (Mattila 15.13-15.16): cone-free sets are rectifiable; hence the cone density Φ_δ(a, V) > 0 at a.e. a.
4. Exceptional sets: {Φ_δ = ∞} has null projection (Vitali covering); {A ∩ (a+V) infinite} has null projection (sibling Eilenberg, k = 0).
5. Key lemma: for a.e. V the trichotomy (Φ_δ ∈ {0, ∞} or a point of A in a + V near a) holds at a.e. a — via the sphere density dichotomy for slab cones, slab-to-cone inclusions, and averaging over O(N) with Haar measure.
6. Transfer from Haar-a.e. g ∈ O(N) to Lebesgue-a.e. frames by O(N)-invariance of Lebesgue measure and right invariance of Haar measure.
7. Combine over δ = 1/i: A is covered by null sets, sets with null projection, and A₃(V).

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
