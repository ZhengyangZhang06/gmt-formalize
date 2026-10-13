<!-- theorem-id: gmt-ch03/root -->

## Theorem `GMT.Ch03.main_theorem`

# Simon GMT, Chapter 3: Countably n-Rectifiable Sets

Prove `GMT.Ch03.main_theorem`, stated in the frozen contract `GMT/Ch03/Contract.lean`, by completing `GMT/Ch03/Submission.lean` (initially a byte copy of the contract). The statement is the conjunction of the chapter's headline results; `GMT/Ch03/README.md` maps each conjunct to the book.

Source: Leon Simon, *Introduction to Geometric Measure Theory* (2014), Chapter 3, printed pages 69–84. Read-only copies for workers: `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt` and `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/simon-gmt.pdf` (printed page = PDF page − 7).

The natural-language proofs already exist in the book: base every natural-language proof and decomposition on Simon's printed proof of the corresponding result (cite the item and the line range in the chapter text), filling in omitted details and correcting printed errata. Only depart from the book where its argument is wrong or incomplete, and say so explicitly.

The pinned `simongmt` package (`Poincare.SimonGMT.*`) contains an earlier kernel-checked partial formalization of the book; its proofs may be reused as library lemmas where they apply. Do not rely on its definitions that the chapter README marks as unfaithful. Toolchain Lean v4.35.0-rc3, Mathlib 25730c7c. Every definition used by the statement must stay byte-identical; only standard axioms are allowed.

Node: `root`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: None (root)

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/21, https://github.com/ZhengyangZhang06/gmt-formalize/issues/22, https://github.com/ZhengyangZhang06/gmt-formalize/issues/23, https://github.com/ZhengyangZhang06/gmt-formalize/issues/24, https://github.com/ZhengyangZhang06/gmt-formalize/issues/25, https://github.com/ZhengyangZhang06/gmt-formalize/issues/26, https://github.com/ZhengyangZhang06/gmt-formalize/issues/27, https://github.com/ZhengyangZhang06/gmt-formalize/issues/28, https://github.com/ZhengyangZhang06/gmt-formalize/issues/29, https://github.com/ZhengyangZhang06/gmt-formalize/issues/30, https://github.com/ZhengyangZhang06/gmt-formalize/issues/31, https://github.com/ZhengyangZhang06/gmt-formalize/issues/32

## Lean problem

Declaration: `GMT.Ch03.main_theorem`

```lean
SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧ SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧ GaussGreenRepresentation ∧ DeGiorgiTheorem
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

# Final proof of `GMT.Ch03.main_theorem` (root node)

Run `20261011T145601Z-8f12588143`, node `root`, issue
<https://github.com/ZhengyangZhang06/gmt-formalize/issues/7>.
Lean target `GMT/Ch03/Submission.lean`; frozen contract `GMT/Ch03/Contract.lean` at the frozen
commit `d09bc8a18ce60face651f042976e8465f21f0f68` (Lean `v4.35.0-rc3`, Mathlib `25730c7c`,
`simongmt` package `2b366308`).

## 1. Statement

```lean
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧
    WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧
    SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧
    BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧
    GaussGreenRepresentation ∧ DeGiorgiTheorem
```

The twelve conjuncts are the headline results of Simon, *Introduction to Geometric Measure
Theory*, Ch. 3 (`chapter-03.txt`): Lemma 1.2 (ll. 25–65), Theorem 1.6 (ll. 109–274),
Theorem 1.9 (ll. 316–323), the area formula (2.4)–(2.5) (ll. 370–401), the co-area formula
(2.8)–(2.9) and Remark 2.10(2) (ll. 412–442), Lemmas 3.2 and 3.3 (ll. 449–496), the
Besicovitch–Federer Theorem 3.6 (ll. 530–536), Theorem 3.8 (ll. 540–548), the Gauss–Green
representation (4.1) (ll. 555–573) and De Giorgi's Theorem 4.3 (ll. 588–746). Every conjunct is a
closed proposition (a `def … : Prop` of the frozen contract); `main_theorem` has no hypotheses.

## 2. The Lean argument actually used

The proof term of `main_theorem` is an anonymous-constructor assembly of eight accepted child
theorems (all in namespace `GMT.Ch03`):

```lean
  ⟨Submission.submanifoldCoverCharacterization_holds,
    Submission.approximateTangentCharacterizations_hold.1,
    Submission.approximateTangentCharacterizations_hold.2,
    Submission.areaFormula_holds,
    Submission.coareaFormula_and_slices_hold.1,
    Submission.coareaFormula_and_slices_hold.2,
    Submission.section3_decomposition_projection_rectifiability.1,
    Submission.section3_decomposition_projection_rectifiability.2.1,
    Submission.besicovitchFedererProjectionTheorem_holds,
    Submission.section3_decomposition_projection_rectifiability.2.2,
    Submission.gaussGreenRepresentation_holds,
    Submission.deGiorgiTheorem_holds⟩
```

| Conjunct (book item) | Supplied by (frozen type of the accepted child) |
|---|---|
| `SubmanifoldCoverCharacterization` (Lemma 1.2) | `submanifoldCoverCharacterization_holds : SubmanifoldCoverCharacterization` |
| `ApproximateTangentCharacterization` (Thm 1.6) | `approximateTangentCharacterizations_hold.1`; type `ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization` |
| `WeightedApproximateTangentCharacterization` (Thm 1.9) | `approximateTangentCharacterizations_hold.2` |
| `AreaFormula` ((2.4)–(2.5)) | `areaFormula_holds : AreaFormula` |
| `CoareaFormula` ((2.8)–(2.9)) | `coareaFormula_and_slices_hold.1`; type `CoareaFormula ∧ SlicesAreRectifiable` |
| `SlicesAreRectifiable` (Rem. 2.10(2)) | `coareaFormula_and_slices_hold.2` |
| `RectifiableDecomposition` (Lemma 3.2) | `section3_decomposition_projection_rectifiability.1`; type `RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ RectifiabilityTheoremForSets` |
| `CoordinateProjectionCriterion` (Lemma 3.3) | `section3_decomposition_projection_rectifiability.2.1` |
| `BesicovitchFedererProjectionTheorem` (Thm 3.6) | `besicovitchFedererProjectionTheorem_holds : BesicovitchFedererProjectionTheorem` |
| `RectifiabilityTheoremForSets` (Thm 3.8) | `section3_decomposition_projection_rectifiability.2.2` |
| `GaussGreenRepresentation` ((4.1)) | `gaussGreenRepresentation_holds : GaussGreenRepresentation` |
| `DeGiorgiTheorem` (Thm 4.3) | `deGiorgiTheorem_holds : DeGiorgiTheorem` |

Each child's type is literally the corresponding contract proposition (or a conjunction of
them, projected with `.1`/`.2`), so the assembly needs no further mathematics: the mathematical
content is entirely in the accepted children, summarized in §4.

### Assumptions

* No hypotheses beyond the frozen contract. The contract's text (everything before
  `main_theorem`) is reproduced byte-for-byte; the only header change is one extra import,
  `Poincare.SimonGMT.Chapter03.SubmanifoldCover` (pinned `simongmt` package), which the accepted
  Lemma 1.2 child uses for the "⇐" direction. I checked that this import does not change the
  elaboration of any frozen constant: elaborating the contract preamble with and without it gives
  identical structural hashes for all 54 constants in `GMT.Ch03` (types, definition bodies and the
  auxiliary `_proof_n` terms). The comparator independently checks equality of every constant
  reachable from the statement (§8).
* Axioms: only `propext`, `Quot.sound`, `Classical.choice` (`#print axioms GMT.Ch03.main_theorem`;
  also checked by the comparator). There is no `sorry`, no new `axiom`, and no change to any
  definition or assumption.
* Besides the accepted theorems, the file contains only build infrastructure local to the section
  that holds them (`set_option`s and one `private` tooling elaborator, §3), which affects
  elaboration metadata and memory use, not the elaborated declarations.

## 3. How this candidate was assembled (integration repair)

The previous root candidate `9831a15e` was produced by line-level Git merges of the twelve
accepted child checkpoints and was rejected by the comparator: the merges had interleaved
fragments of different proofs (in `Submission.setIntegral_blowUpMap_image`,
`gaussGreenRep_divergence_integral_local_bound`, `areaFormula_on_chart_piece`,
`bf_coneMass_slab_cover` and `rectifiable_of_approx_tangent_measure`), declared
`setIntegral_blowUpMap_image`, `gaussGreenRep_divergence_integral_local_bound` and
`bf_coneMass_slab_cover` twice (garbled first copies), placed several helpers (e.g.
`gaussGreenRep_c1_uniform_approx`, `lipschitz_uniform_remainder_on_closed_subset`) after their
first use, and left the child theorems *after* `main_theorem` (each child checkpoint places its own
theorem after the contract's `main_theorem := by sorry`), so `main_theorem` could not see them.

This candidate replaces the merged text by a clean union of the accepted checkpoints:

* Sources: the accepted candidate commits of the twelve direct children —
  `c1_approximation` `849b6ec060`, `eilenberg_inequality` `c2a19cb278`,
  `rectifiable_of_tangent_measure` `f0931a9d98`, `chart_tangent_differential` `89498ad9db`,
  `submanifold_cover` `504efa5909`, `tangent_characterizations` `fe8fba36e3`,
  `area_formula` `fd34bbfe66`, `coarea_and_slices` `a6297ede5f`, `besicovitch_federer`
  `b633a94f45`, `section3_consequences` `9477567347`, `gauss_green` `eef5ae893c`,
  `de_giorgi` `f33bed6a50`. Each of these files compiled and passed its own comparator check.
* Each file was split into top-level declarations. Every declaration occurring in several
  checkpoints has the same text in all of them (the only differences were trailing blank lines),
  so the union is well defined: 226 theorems, exactly the 226 accepted DAG nodes below the root
  (every accepted `lean_name` occurs exactly once; no other theorem was added — the only other new
  declaration is the `private` tooling elaborator described below; no duplicated namespace or
  placeholder scaffold remains). Statements and proof bodies are copied verbatim — no
  proof was edited.
* Order: first occurrence when reading the checkpoints in the DAG order above. This is a valid
  dependency order because every checkpoint compiled in its own order; I also extracted the 250
  references between the 226 declarations from the comment-stripped source and checked that none
  points forward.
* The 226 declarations sit in `section AcceptedChildDeclarations … end AcceptedChildDeclarations`;
  `main_theorem` comes after the section, followed by `end GMT.Ch03`.

**Memory (build infrastructure only).** The first comparator run of the plain union was killed by
the out-of-memory killer (`Lean exited with code 137`): the verification workers run in a container
whose cgroup limit is 3.5 GB, and Lean's command-line driver keeps the info tree of every command
until the end of the file (to write the `.ilean`). Measured with `LEAN_NUM_THREADS=4`, the plain
20k-line file reaches 2.67 GB of anonymous memory plus ~1.6 GB of mapped `.olean`s, i.e. it only
fits by thrashing. The section therefore starts with

* `set_option Elab.async false` (elaborate the declarations one at a time),
* a `private` command elaborator `elabDeclarationWithoutInfoTrees`, registered with
  `@[local command_elab Lean.Parser.Command.declaration]`, which turns info-tree recording off,
  calls Lean's builtin `Lean.Elab.Command.elabDeclaration` on the unchanged syntax, and restores the
  flag,
* `set_option linter.unusedTactic false` (Mathlib) and `set_option linter.unreachableTactic false`
  (Batteries), the two linters that read tactic info trees and would otherwise report every
  tactic as unused or never executed.

Info trees are editor metadata (hover, go-to-definition, `.ilean` references); the elaborated
declarations are unchanged and every one is still checked by the kernel. The elaborator is a
tooling `def`, not a theorem, is not reachable from `main_theorem` (so it is not part of the
comparator's export), and everything is local to the section: after `end
AcceptedChildDeclarations` the builtin elaborator is the only one for declarations and
`Elab.async` is back at its default, so `main_theorem` is elaborated with the default settings
(both facts checked with a probe on a test slice). On a 5.8k-line slice the peak anonymous memory
drops from 986 MB to 412 MB (import baseline 257 MB); on the full file from 2.67 GB to
0.6–0.7 GB (694 MB and 615 MB in two runs).

## 4. Proof of each conjunct (the accepted children)

Each child below has its own reviewed natural-language proof (`parent-supplied-natural-proof.md`
under `.humanize-workspace/20261011t145601z-8f12588143/root/children/<child>/` and the run's
`nodes/<child>/`), its own decomposition into accepted grandchildren, and a kernel-checked Lean
proof that passed the comparator for its frozen type. The summaries below describe the routes of
the Lean proofs as documented in the declarations' docstrings; departures from the book are
stated.

### 4.0 Four shared auxiliary results (not used directly by `main_theorem`)

* **`lipschitz_c1_approximation`** (issue #21; Simon Ch. 2, Thm 1.5): every Lipschitz
  `f : ℝⁿ → ℝᵖ` agrees, together with its derivative, with a `C¹` map outside a set of
  arbitrarily small Lebesgue measure. Coordinatewise reduction to the scalar case
  `lipschitz_real_c1_approximation`: Rademacher (Mathlib `LipschitzWith.ae_differentiableAt`),
  Lusin for `Df`, and Egoroff for the Taylor remainders give a closed `A` with the uniform
  remainder estimate 1.6(‡); Whitney's extension theorem (Ch. 2, 1.6) is proved inline: off `A`,
  `g` averages the jets `f(p) + Df(p)(· − p)` at nearest points `p ∈ A` with a partition of unity
  (Mathlib `ContDiffBump`) on Vitali-selected balls `B(c, min(1, d(c, A))/100)` of bounded overlap.
* **`eilenberg_upper_integral_inequality`** (issue #22; Ch. 2, 1.8–1.9): for an `L`-Lipschitz
  `f : ℝᴺ → ℝᵐ` and any `A`, a Borel `g ≥ Hᵏ(A ∩ f⁻¹{y})` with `∫ g ≤ C Lᵐ H^{m+k}(A)`: near-optimal
  covers `Cᵢⱼ`, `gᵢ = ∑ⱼ diam(Cᵢⱼ)ᵏ 1_{closure f(Cᵢⱼ)}`, `g = liminf gᵢ`, Fatou, and
  `Lᵐ(closure S) ≤ ωₘ (diam S)ᵐ` in place of the isodiametric inequality; the cases
  `H^{m+k}(A) = ∞` and `L = 0` are treated directly.
* **`rectifiable_of_approx_tangent_measure`** (issue #23; the measure form of Thm 1.6 "⇐",
  ll. 145–274, with Remark 1.5(3)): a locally finite Borel measure with approximate tangent
  planes of positive multiplicity a.e. is carried by a Borel countably `n`-rectifiable set. For
  `n = 0` the lower density bound makes `μ` atomic. For `n ≥ 1`: a countable `1/16`-net of
  `n`-planes, the sets where the density and cone bounds of Simon (9) hold uniformly below a
  scale, bi-Lipschitz projection onto a net plane on each such set (Simon (10), with the corrected
  constant `b = a/(2·32ⁿ)`), hence countably many Lipschitz graphs.
* **`chart_approx_tangent_and_differential`** (issue #24; Remarks 1.5(2), 1.8(1), Ch. 2
  (4.8)–(4.10)): for a `C¹` immersion `ψ` and a.e. parameter `u` with `ψ(u) ∈ M`, (A) `range Dψ(u)`
  is the weighted approximate tangent space of `M` at `ψ(u)`, (B) `f ∘ ψ` is differentiable at `u`,
  (C) `D(f∘ψ)(u)w` is the line derivative of `f` at `ψ(u)` in direction `Dψ(u)w`. (A): local
  bi-Lipschitz balls, the upper-density theorem and Lebesgue differentiation give the density
  conditions a.e. on `M ∩ ψ(B)`, and the blow-ups of the `C¹` piece converge to `range Dψ(u)`.

### 4.1 Lemma 1.2 — `submanifoldCoverCharacterization_holds` (issue #25)

"⇐": `Poincare.SimonGMT.Chapter03.countablyRectifiable_of_submanifold_cover` (pinned library;
`Chapter02.IsSimonSubmanifold 1` is `IsC1Submanifold n` with the conditions reordered). "⇒":
`lipschitz_c1_approximation` gives `C¹` maps `Gⱼᵢ` with `Lⁿ{Fⱼ ≠ Gⱼᵢ} < 1/i`; with
`Zⱼ = ℝⁿ ∖ ⋃ᵢ {Fⱼ = Gⱼᵢ}`, `Fⱼ(ℝⁿ) ⊆ Fⱼ(Zⱼ) ∪ ⋃ᵢ Gⱼᵢ(ℝⁿ)` and `Hⁿ(Fⱼ(Zⱼ)) = 0` (erratum: the
book's (1) is printed as `graph Fⱼ ⊂ Eⱼ ∩ …`). For one `C¹` map `G`
(`c1_range_null_union_submanifolds`): the critical image is `Hⁿ`-null — Mathlib's
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` cuts the critical set into pieces on
which `G` is `δ`-close to a non-injective linear map, and a stretch along its kernel gives
`Hⁿ(G(P)) ≤ (‖A‖+1)ⁿ δ Lⁿ(P)`; each regular point has a ball whose image is an embedded `C¹`
submanifold; Lindelöf gives countably many.

### 4.2 Theorems 1.6 and 1.9 — `approximateTangentCharacterizations_hold` (issue #26)

Theorem 1.9 is proved first and Theorem 1.6 is its case `θ ≡ 1` (admissible because
`Hⁿ(M ∩ K) < ∞`, and then Def. 1.7 is Def. 1.4). "⇒": Lemma 1.2 gives `M ⊆ N₀ ∪ ⋃ⱼ Nⱼ`; in every
`C¹` chart the weighted tangent plane at `ψ(u)` is `range Dψ(u)` for a.e. `u`
(`chart_approx_tangent_and_differential` with `f = 0`), and the chartwise transfer
`ae_of_ae_on_submanifold_charts` (Lindelöf; chart images of `Lⁿ`-null sets are `Hⁿ`-null) makes
this `Hⁿ`-a.e. on `M`. "⇐": `μ = θ Hⁿ⌞M` is finite on compacts, has the null sets
`{S : Hⁿ(M ∩ S) = 0}`, and has approximate tangent plane `P` with multiplicity `θ(x) > 0` wherever
`M` has weighted tangent plane `P` (change of variables under `η_{x,r}`,
`weightedMeasure_finite_null_tangent`); `rectifiable_of_approx_tangent_measure` gives a Borel
rectifiable `R` with `μ(Rᶜ) = 0`, i.e. `Hⁿ(M ∖ R) = 0`.

### 4.3 Area formula — `areaFormula_holds` (issue #27)

Lemma 1.2 and `areaFormula_good_chart_pieces` cover `M`, up to an `Hⁿ`-null set, by countably
many compact chart pieces `ψ_α(D_α)` with `ψ_α` bi-Lipschitz and `f ∘ ψ_α` Lipschitz. At a.e.
parameter, `chart_approx_tangent_and_differential` and `areaFormula_chart_jacobian_identity`
(uniqueness of tangent spaces and line derivatives; Mathlib `LinearMap.normDet_comp`) give
`T_xM = range Dψ_α(u)`, the tangential differential, and `J^M_f(ψ_α u)·Jψ_α(u) = J(f∘ψ_α)(u)`;
this proves (a). On one piece (`areaFormula_on_chart_piece`) the weighted area formula with
multiplicity of Simon Ch. 2 (3.2), (3.4)–(3.5) is applied to `ψ_α` and `f ∘ ψ_α`; since the SimonGMT
modules proving it are not imported, it is derived in the file from the linear case (Mathlib
`LinearMap.euclideanHausdorffMeasure_image`) by comparison with linear maps on the pieces of
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`. `areaFormula_glue_pieces` sums over
the pieces; the uncovered part and its image are `Hⁿ`-null
(`areaFormula_image_null_of_locallyLipschitzOn`); (2.4) is the case `h ≡ 1`. Erratum: outer
integrals over the target `ℝ^{n+ℓ₁}`.

### 4.4 Co-area formula and slices — `coareaFormula_and_slices_hold` (issue #28)

`rectifiable_c1_chart_pieces` (Lemma 1.2 and `lipschitz_c1_approximation`) covers `M`, up to an
`Hⁿ`-null set, by Borel pieces `ψ_j(E_j)` of injective `C¹` charts on which `f ∘ ψ_j` agrees to
first order with a `C¹` map `G_j`. (a) is `coarea_tangent_existence` (chart lemma plus
`chart_coarea_jacobian_identification`). On one piece, `chart_piece_coarea_formula` combines the
`C¹` parametric co-area formula `c1_parametric_coarea_formula` (Simon Ch. 2, 6.3/6.6, whose proof
Simon omits: critical part with `Hᵏ`-null slices for a.e. `y` via a cube-subdivision covering,
implicit-function charts, the flat Jacobian identity, Tonelli on `ℝᵐ × ℝᵏ` and change of
variables) with the injective `C¹` area formula and Lusin–Souslin, and the Jacobian identification
`J^{M*}_f(ψ u)·Jψ(u) = normDet(Dψ(u)∘ι_{ker DG(u)})·normDet(DG(u)*)`. `coarea_gluing_of_pieces`
sums the pieces, null sets having `Hᵏ`-null slices for a.e. `y` by
`coarea_null_slices_of_eilenberg` (Eilenberg's inequality applied to Lipschitz extensions,
`LipschitzOnWith.extend_finite_dimension`); (2.8) is (2.9) with `g ≡ 1`; `m = 0` is direct.
Slices: `c1_level_slices_countablyRectifiable` (regular parts are implicit-function `C¹` images,
critical parts are `Hᵏ`-null for a.e. `y`). Erratum: (2.9) is stated with `A` on both sides.

### 4.5 Besicovitch–Federer — `besicovitchFedererProjectionTheorem_holds` (issue #29)

The book gives no proof (l. 536: "see [Fed69] or [Ros84]"); the accepted proof follows P. Mattila,
*Geometry of Sets and Measures in Euclidean Spaces*, Ch. 15 and 18, as presented in M. G.
Dall'Alba, *The Besicovitch–Federer Projection Theorem* (Padova 2020), Thm. 5.1. Step 0: `n = 0`
forces `Q = ∅`, `ℓ = 0` forces `Hⁿ(Q) = 0`. Step 1 (`bf_compact_cover_reduction`): Borel hulls and
SimonGMT's measurable Lemma 3.2 (`measurable_rectifiable_purelyUnrectifiable_decomposition`) plus
inner regularity cover `Q` by a null set and compact purely unrectifiable sets of finite measure.
Steps 2–10 (`bf_compact_projection_null`): cone-free sets are rectifiable, so the cone density is
positive a.e.; where it is infinite the projection is null (Vitali covering); the cone trichotomy
holds for a.e. frame (`bf_coneTrichotomy_ae_frames`: sphere density dichotomy for slab cones,
averaging over `O(N)` with Haar measure (Mathlib `Measure.haarMeasure`) and transfer to
Lebesgue-a.e. frames, the contract's encoding `ForAlmostAllProjections` of "σ-a.e. projection");
so outside null sets every point has an infinite fibre, and infinite fibres have null projection
by `eilenberg_upper_integral_inequality` (`k = 0`).

### 4.6 Lemmas 3.2, 3.3 and Theorem 3.8 — `section3_decomposition_projection_rectifiability` (issue #30)

3.2 (`section3_rectifiableDecomposition`): `Poincare.SimonGMT.Chapter03.simon_lemma_3_2` with the
cover `(Aⱼ)`. 3.3 (`section3_coordinateProjectionCriterion_of_submanifoldCover`): by Lemma 1.2 and
Lindelöf it suffices that `R ∩ Nⱼ ∩ W = ψ(T)` is null for each chart `ψ : V → W`; if `Lⁿ(T) = 0`
then `Hⁿ(ψ(T)) = 0` (`C¹` images of null sets); otherwise some coordinate projection `p_J` with
`#J = n` is injective on the tangent plane, `p_J ∘ ψ` is anti-Lipschitz near a density point of `T`,
and `Hⁿ(p_J(S)) > 0`, a contradiction. 3.8
(`section3_rectifiabilityTheorem_of_besicovitchFederer`): split `A = R ∪ P` by 3.2; by 3.6,
`Hⁿ(p(P)) = 0` for almost all `p`, so the hypothesis with `B = P` forces `Hⁿ(P) = 0`. Erratum:
l. 540 "by combining 3.2 and 3.7" should read "3.2 and 3.6".

### 4.7 Gauss–Green representation — `gaussGreenRepresentation_holds` (issue #31)

"⇐" (`gaussGreenRep_isLocallyBV_of_pair`): the pair identity bounds `∫_W χ_E div g` by
`μ(W̄) sup|g|`. "⇒": the BV bound extends `g ↦ ∫_{E∩U} div g` from `C¹` fields to a locally bounded
functional `Λ` on continuous compactly supported fields (`gaussGreenRep_bv_functional_extension`,
uniform `C¹` approximation); the Riesz representation on the open set `U`
(`gaussGreenRep_riesz_on_open`, Simon Ch. 1, 4.14) gives `Λ g = ∫⟨g, ν₀⟩ dμ`, and the pair is
`(μ, −ν₀)`. The vector Riesz step (`gaussGreenRep_riesz_sigmaCompact_borel`) splits each component
functional into positive parts, represents them with Mathlib's Riesz–Markov–Kakutani
`RealRMK.rieszMeasure`, and takes Radon–Nikodym densities and the polar decomposition.
Uniqueness: two pairs pair equally with continuous fields (`gaussGreenRep_pairing_eq_continuous`);
the variation formula `μ(O) = sup ∫⟨g, ν⟩ dμ` (`gaussGreenRep_measure_eq_iSup_pairing`, Lusin and a
unit-field extension) makes the measures agree on open subsets of `U`, hence everywhere
(`gaussGreenRep_measure_eq_of_open_eq`, π–λ); the normals agree `μ`-a.e. by the fundamental lemma
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`).

### 4.8 De Giorgi — `deGiorgiTheorem_holds` (issue #32)

A pair exists by 4.7. For any pair `(μ, ν)` and `x ∈ ∂*E`: the density estimates
(`deGiorgi_density_estimates`: Simon (1)–(6), (10), (11), using the complement pair `(μ, −ν)` of
`U ∖ E`, an upper mass bound, and a lower volume bound from an `L¹` Sobolev inequality for `ζχ_G`,
the Gagliardo–Nirenberg–Sobolev inequality being proved in the file because Mathlib's
`SobolevInequality` module is not imported); compactness of the blow-ups `η_{x,r}(E)` in `L¹_loc`
(`deGiorgi_indicator_compactness`: translation estimates, mollification, diagonal
Arzelà–Ascoli); half-space rigidity of every limit (`deGiorgi_halfSpace_rigidity`), giving (‡‡)
(`deGiorgi_blowUp_tendsto_halfSpace`; erratum: (9) and the final display must read
`{x^{n+1} > λ}`, `{x^{n+1} > 0}`); (‡) with multiplicity 1 from the blow-up Gauss–Green identity,
the excess decay and the mass bound (`deGiorgi_tangent_measure`). Then `∂*E` is Borel
(`deGiorgi_measurableSet_reducedBoundary`) and carries `μ` (`deGiorgi_measure_compl_reducedBoundary`,
Lebesgue–Besicovitch differentiation), and `deGiorgi_rectifiable_measure_eq_hausdorff` — which
takes `rectifiable_of_approx_tangent_measure` and `approximateTangentCharacterizations_hold.1` as
inputs — gives rectifiability of `∂*E` and `μ = Hⁿ⌞∂*E` via `Hⁿ(A) ≤ μ(A) ≤ 2ⁿHⁿ(A)` on `∂*E` and a
density comparison (Mathlib `Besicovitch.ae_tendsto_rnDeriv`). This completes the book's sketch at
l. 604 ("By 1.6 and 3.6 of Ch. 1").

### Dependency structure (extracted from the Lean source)

Lemma 1.2 ← `lipschitz_c1_approximation`; 1.6/1.9 ← Lemma 1.2,
`rectifiable_of_approx_tangent_measure`, `chart_approx_tangent_and_differential`; area ← Lemma 1.2,
chart lemma; co-area/slices ← Lemma 1.2, `lipschitz_c1_approximation`,
`eilenberg_upper_integral_inequality`, chart lemma; 3.6 ← Eilenberg; 3.2/3.3/3.8 ← Lemma 1.2, 3.6;
(4.1) ← none; 4.3 ← (4.1), `rectifiable_of_approx_tangent_measure`, 1.6/1.9. The graph is acyclic,
and no child depends on `main_theorem`.

## 5. Historical decomposition versus lemmas actually used

* The root's accepted outline (`nodes/root/natural-proof-source.md`: "follow the published proof"
  for each of the twelve conjuncts) and plan (`nodes/root/plan-source.md`: decompose along the
  conjuncts) are unchanged history; the reviewed decomposition is `nodes/root/decomposition-v1.json`
  (12 children). The final Lean route is exactly that decomposition.
* Of the 226 accepted declarations, 225 are reachable from `main_theorem`. The exception is
  `Submission.gaussGreenRep_riesz_caratheodory_borel_version` (node
  `root.gauss_green-a1.riesz_on_open-a1.caratheodory_borel_version-a1`), which its parent's final
  proof does not use; it is kept unchanged to preserve the accepted child interface.
* Where a child's reviewed outline named a library lemma that the final Lean proof does not use,
  the Lean route is the one stated in §4: Whitney's extension theorem is proved inline (not taken
  from SimonGMT), the Riesz step uses Mathlib's `RealRMK.rieszMeasure` (not SimonGMT's Ch. 1,
  4.14), and the Lipschitz area formula on parameter domains is derived in the file from Mathlib's
  linear case (not SimonGMT's Ch. 2 area formula).

## 6. Library reuse provenance

All reused library results are existing, pinned declarations, used with their own proofs:

* `simongmt` (`Poincare.SimonGMT`, rev `2b3663083f3f`):
  `Chapter03.countablyRectifiable_of_submanifold_cover` (Lemma 1.2 "⇐"),
  `Chapter03.simon_lemma_3_2` (Lemma 3.2),
  `Chapter03.measurable_rectifiable_purelyUnrectifiable_decomposition` (3.6, Step 1),
  `Chapter03.HasWeightedApproximateTangentSpaceAt.unique`, `Chapter03.countablyRectifiable_iUnion`,
  `countablyRectifiable_sUnion`, `countablyRectifiable_range`, `countablyRectifiable_of_measure_zero`,
  `Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule`,
  `Chapter03.support_euclideanHausdorffMeasure_restrict_submodule`,
  `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn`, and the divergence API used by the
  contract (`Chapter02.euclideanDivergence`, `euclideanDivergence_eq_sum_inner`,
  `support_euclideanDivergence_subset`, `compactlySupportedSupNorm`).
* Mathlib (rev `25730c7c`), e.g. `LipschitzWith.ae_differentiableAt` (Rademacher),
  `LinearMap.normDet_comp`/`normDet_sq`, `LinearMap.euclideanHausdorffMeasure_image`,
  `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, `Besicovitch.ae_tendsto_rnDeriv`,
  Vitali covering `exists_disjoint_covering_ae`, `Measure.haarMeasure`, `RealRMK.rieszMeasure`,
  `ContDiffBump`, `LipschitzOnWith.extend_finite_dimension`,
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.

## 7. Reference use

`reference_use` (exactly one entry):

* **source:** `local-project` — snapshot
  `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063`
  (manifest: project `d09bc8a18ce6`, mathlib `25730c7c759d`).
  **Queries and findings:**
  `cmp project/GMT/Ch03/Contract.lean <frozen contract>` — identical (the snapshot's
  `Submission.lean` is also a byte copy of the contract);
  `rg -n "theorem Submission\." project/GMT/` — **no match** (all 226 helper declarations come
  from this run's accepted checkpoints, none from the snapshot);
  `rg -n "SubmanifoldCover" project/GMT/Ch03/README.md` — ll. 16, 29: Lemma 1.2 "⇐" is
  `Chapter03.countablyRectifiable_of_submanifold_cover` in `Chapter03/SubmanifoldCover.lean`
  (justifies the one added import);
  `rg -l "CountablyRectifiable|PurelyUnrectifiable" mathlib/Mathlib/{MeasureTheory,Analysis,Topology}`
  — **no match** (rectifiability is not in Mathlib; it comes from `simongmt` and this run);
  `rg -n "SobolevInequality|RieszMarkovKakutani" project/GMT/Ch03/` — **no match** (neither is
  imported by the contract);
  `rg -n "def rieszMeasure" mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/` —
  `Real.lean:65` (`RealRMK.rieszMeasure`, used in 4.7);
  `rg -n "theorem ae_tendsto_rnDeriv" mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean` —
  l. 1078 (used in 4.8);
  `rg -n "theorem LipschitzWith.ae_differentiableAt" mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
  — l. 385; `rg -n "theorem normDet_comp|theorem normDet_sq" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
  — ll. 294, 324; `rg -n "def haarMeasure" mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean` —
  l. 520; `rg -n "theorem exists_disjoint_covering_ae" mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
  — l. 237.
  Compatibility: every cited declaration is from the pinned Mathlib/`simongmt` revisions used by the
  build, and the comparator's axiom check covers them.

## 8. Verification

All results below are for the final Lean file (`GMT/Ch03/Submission.lean`, sha256
`52570fbc08aa2426aea30dfe5cd74b81fb93039497c9e7ae4d0c2bca3a601ebf`, first committed in
`57b4774c`).

* Exact configured comparator (`gmt-compare.py … --frozen-commit d09bc8a18ce6… root`) on
  candidate `57b4774cbad5f63e80eab4fbba49a6f1a8ef72e7`: **passed** — "GMT comparator: comparator
  and Lean kernel accepted GMT.Ch03.main_theorem", "Your solution is okay!", exit 0; checks
  `exit_zero`, `lean_kernel_accepted`, `final_marker` all true; evidence
  `cluster-state/verification/results/hoa43/20261013T033609Z-ch03-root-a05df1dl`, verdict key
  `d63da00fc3d55975a3e30dedbaa37185eaf61e7fc5e7f37cd6847300efe93384`. (The earlier run on
  `33bd0e72`, before the memory change, was killed by the OOM killer: evidence
  `…/20261013T020812Z-ch03-root-ae40ge3k`.)
* Local `lake build GMT.Ch03.Submission` with `LEAN_NUM_THREADS=4`: succeeded; the module built in
  542 s with peak anonymous memory 615 MB; no errors, no `sorry`, and no diagnostics from
  `Submission.lean` other than the four module-system import notes that the frozen contract itself
  produces.
* `#print axioms GMT.Ch03.main_theorem`: `[propext, Classical.choice, Quot.sound]`.
* Child interfaces: all 226 accepted children's frozen `lean_statement`s (from the run's
  `dag.json`, normalized by the workflow validator `lean_contract.py`) were elaborated in the
  comparator's replayed contract scope after `import GMT.Ch03.Submission` and closed by
  `exact Submission.<lean_name>`: 226/226 succeed, 0 errors.

## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Root delivery: merge the exact checked root PR, confirm the remote tree, then link and close child review PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
