<!-- theorem-id: gmt-ch03/root.area_formula-a1.good_chart_pieces-a1 -->

## Theorem `Submission.areaFormula_good_chart_pieces`

Let n, N, p ∈ ℕ, M, U, N₀ ⊆ ℝ^N, (S_j)_{j∈ℕ} subsets of ℝ^N and f : ℝ^N → ℝ^p. Assume:
- U is open and M ⊆ U;
- f is locally Lipschitz on U;
- every S_j is an n-dimensional embedded C¹ submanifold of ℝ^N (IsC1Submanifold n (S j));
- M ⊆ N₀ ∪ ⋃_j S_j.

Then there are sets V_α, D_α ⊆ ℝⁿ, maps ψ_α : ℝⁿ → ℝ^N and constants K_α, C_α ∈ ℝ≥0 (α ∈ ℕ) such that M ⊆ N₀ ∪ ⋃_α ψ_α(D_α), and for every α:
- V_α is open, ψ_α is C¹ on V_α, and Dψ_α(u) is injective for all u ∈ V_α;
- D_α is compact and D_α ⊆ V_α;
- ψ_α is K_α-Lipschitz on D_α, and |u − v| ≤ C_α·|ψ_α(u) − ψ_α(v)| for all u, v ∈ D_α;
- f∘ψ_α is K_α-Lipschitz on D_α.

Node: `root.area_formula-a1.good_chart_pieces-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/27

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.areaFormula_good_chart_pieces`

```lean
∀ (n N p : ℕ) (M U N₀ : Set (Rn N)) (S : ℕ → Set (Rn N)) (f : Rn N → Rn p), IsOpen U → M ⊆ U → LocallyLipschitzOn U f → (∀ j, IsC1Submanifold n (S j)) → M ⊆ N₀ ∪ ⋃ j, S j → ∃ (V D : ℕ → Set (Rn n)) (ψ : ℕ → Rn n → Rn N) (K C : ℕ → ℝ≥0), (∀ α, IsOpen (V α) ∧ ContDiffOn ℝ 1 (ψ α) (V α) ∧ (∀ u ∈ V α, Function.Injective (fderiv ℝ (ψ α) u)) ∧ IsCompact (D α) ∧ D α ⊆ V α ∧ LipschitzOnWith (K α) (ψ α) (D α) ∧ (∀ u ∈ D α, ∀ v ∈ D α, dist u v ≤ (C α : ℝ) * dist (ψ α u) (ψ α v)) ∧ LipschitzOnWith (K α) (f ∘ ψ α) (D α)) ∧ M ⊆ N₀ ∪ ⋃ α, ψ α '' D α
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

- Parent DAG node: `root.area_formula-a1`
- Child DAG node: `root.area_formula-a1.good_chart_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 1 of the parent proof (“Good chart balls”). It makes explicit the local-chart argument of the “if” part of Simon Ch. 3, Lemma 1.2 (chapter-03.txt lines 25-35): “for each x ∈ N there is ρ_x > 0 such that B_{ρ_x}(x) ∩ N = ψ(V) for suitable C¹ map ψ : V → ℝ^{n+ℓ}, V ⊆ ℝⁿ open. Since such C¹ maps are automatically Lipschitz in each closed ball ⊂ V …”. The submanifolds are embedded C¹ submanifolds in the sense of Simon Ch. 2 (4.1) (contract IsC1Submanifold). The argument also uses the Lindelöf property of ℝⁿ and ℝ^N and the mean value inequality, which is the bi-Lipschitz estimate of the parent's Step 1(i).

Notation.
- ℝ^d = Rn d = EuclideanSpace ℝ (Fin d), with Euclidean norm |·| and distance.
- B_r(u) and B̄_r(u) are the open and closed balls.
- Dψ(u) = fderiv ℝ ψ u, and ‖·‖ is the operator norm.

Of IsC1Submanifold n S_j only these parts are used: V open, W open with y ∈ W, ψ C¹ on V, ψ(V) = W ∩ S_j, and Dψ(u) injective for u ∈ V. Injectivity of ψ on V and properness are not used.

Proof.
1. Countably many charts. Fix j. For each y ∈ S_j, IsC1Submanifold n (S_j) provides V_y ⊆ ℝⁿ open, W_y ⊆ ℝ^N open with y ∈ W_y, and ψ_y : ℝⁿ → ℝ^N that is C¹ on V_y, with ψ_y(V_y) = W_y ∩ S_j and Dψ_y(u) injective for all u ∈ V_y. Since ℝ^N is second countable, there is a countable T_j ⊆ S_j with ⋃_{y∈T_j} W_y = ⋃_{y∈S_j} W_y ⊇ S_j (Mathlib TopologicalSpace.isOpen_biUnion_countable). Hence S_j = ⋃_{y∈T_j} (W_y ∩ S_j) = ⋃_{y∈T_j} ψ_y(V_y). Let 𝒞 := {(j, y) : j ∈ ℕ, y ∈ T_j}, a countable set, and write (V_c, ψ_c) for the chart of c ∈ 𝒞. Then ⋃_j S_j ⊆ ⋃_{c∈𝒞} ψ_c(V_c).
2. A good closed ball at one parameter. Fix c ∈ 𝒞 and u₀ ∈ V_c with ψ_c(u₀) ∈ U. Write V := V_c, ψ := ψ_c, A := Dψ(u₀). We produce r > 0 and K, C ∈ ℝ≥0 with:
 (i) B̄_r(u₀) ⊆ V;
 (ii) ψ is K-Lipschitz on B̄_r(u₀);
 (iii) |u − v| ≤ C|ψ(u) − ψ(v)| for all u, v ∈ B̄_r(u₀);
 (iv) f∘ψ is K-Lipschitz on B̄_r(u₀).
 (a) A is linear and injective on the finite-dimensional ℝⁿ, so there is K_A > 0 with |w| ≤ K_A|Aw| for all w (Mathlib LinearMap.exists_antilipschitzWith; this also covers n = 0). Put m := 1/K_A > 0. Then |Aw| ≥ m|w|.
 (b) ψ is C¹ on the open V, so z ↦ Dψ(z) is continuous on V (Mathlib ContDiffOn.continuousOn_fderiv_of_isOpen). Choose r₁ > 0 with B̄_{r₁}(u₀) ⊆ V and ‖Dψ(z) − A‖ ≤ m/2 for z ∈ B̄_{r₁}(u₀). The map z ↦ ψ(z) − Az is differentiable at each point of the convex set B̄_{r₁}(u₀), with derivative Dψ(z) − A of norm ≤ m/2. By the mean value inequality (Mathlib Convex.norm_image_sub_le_of_norm_fderiv_le), |ψ(u) − ψ(v) − A(u − v)| ≤ (m/2)|u − v| for u, v ∈ B̄_{r₁}(u₀). Consequently, for such u, v:
 - |ψ(u) − ψ(v)| ≥ |A(u − v)| − (m/2)|u − v| ≥ (m/2)|u − v|;
 - |ψ(u) − ψ(v)| ≤ (‖A‖ + m/2)|u − v|.
 (c) Let x₀ := ψ(u₀) ∈ U. Since f is locally Lipschitz on U, there are L_f ≥ 0 and t ∈ 𝓝[U] x₀ with f L_f-Lipschitz on t. As U is open and x₀ ∈ U, 𝓝[U] x₀ = 𝓝 x₀, so B_s(x₀) ⊆ t for some s > 0. ψ is continuous at u₀ (it is differentiable there), so there is r with 0 < r ≤ r₁ and ψ(B̄_r(u₀)) ⊆ B_s(x₀).
 (d) Put K := (‖A‖ + m/2) + L_f·(‖A‖ + m/2) and C := 2K_A = 2/m. Then:
 - (i) holds because r ≤ r₁.
 - On B̄_r(u₀) ⊆ B̄_{r₁}(u₀), (b) gives |ψ(u) − ψ(v)| ≤ (‖A‖ + m/2)|u − v| ≤ K|u − v|, which is (ii), and |u − v| ≤ (2/m)|ψ(u) − ψ(v)|, which is (iii).
 - For u, v ∈ B̄_r(u₀), the points ψ(u), ψ(v) lie in B_s(x₀) ⊆ t. So |f(ψ(u)) − f(ψ(v))| ≤ L_f|ψ(u) − ψ(v)| ≤ L_f(‖A‖ + m/2)|u − v| ≤ K|u − v|, which is (iv).
3. Countably many balls per chart. For c ∈ 𝒞, the set O_c := V_c ∩ ψ_c⁻¹(U) is open, because ψ_c is continuous on the open V_c and U is open (Mathlib ContinuousOn.isOpen_inter_preimage). For u₀ ∈ O_c let r(c, u₀), K(c, u₀), C(c, u₀) be as in Step 2. The open balls B_{r(c,u₀)}(u₀), u₀ ∈ O_c, cover O_c. By second countability of ℝⁿ there is a countable Q_c ⊆ O_c with O_c ⊆ ⋃_{u₀∈Q_c} B_{r(c,u₀)}(u₀).
4. Enumeration. The set Π := {(c, u₀) : c ∈ 𝒞, u₀ ∈ Q_c} is countable. To π = (c, u₀) ∈ Π associate V_π := V_c, ψ_π := ψ_c, D_π := B̄_{r(c,u₀)}(u₀), K_π := K(c, u₀), C_π := C(c, u₀).
 - If Π ≠ ∅, choose a surjection α ↦ π_α from ℕ onto Π (Mathlib Set.Countable.exists_eq_range) and set (V_α, D_α, ψ_α, K_α, C_α) := (V_{π_α}, D_{π_α}, ψ_{π_α}, K_{π_α}, C_{π_α}).
 - If Π = ∅, set V_α = D_α = ∅, ψ_α = 0 and K_α = C_α = 0 for all α.
5. Per-piece properties.
 - If Π = ∅, every per-piece condition holds vacuously: ∅ is open and compact, ∅ ⊆ ∅, every map is C¹ and Lipschitz on ∅, and statements quantified over u ∈ ∅ are trivially true.
 - Otherwise π_α = (c, u₀). V_α = V_c is open, ψ_α = ψ_c is C¹ on V_α, and Dψ_α(u) is injective for u ∈ V_α (Step 1). D_α = B̄_{r(c,u₀)}(u₀) is closed and bounded in ℝⁿ, hence compact, and D_α ⊆ V_α by Step 2(i). ψ_α and f∘ψ_α are K_α-Lipschitz on D_α, and |u − v| ≤ C_α|ψ_α(u) − ψ_α(v)| on D_α, by Step 2(ii)-(iv).
6. Covering. Let x ∈ M with x ∉ N₀. As M ⊆ N₀ ∪ ⋃_j S_j, x ∈ S_j for some j, so by Step 1 x = ψ_c(u) for some c ∈ 𝒞 and u ∈ V_c. Since x ∈ M ⊆ U, we have u ∈ O_c, so by Step 3 u ∈ B_{r(c,u₀)}(u₀) ⊆ D_{(c,u₀)} for some u₀ ∈ Q_c. In particular Π ≠ ∅ and (c, u₀) = π_α for some α, so x = ψ_α(u) ∈ ψ_α(D_α). Hence M ⊆ N₀ ∪ ⋃_α ψ_α(D_α). When Π = ∅ the same argument shows M ⊆ N₀. ∎

Appendix: formalization aid, not part of the mathematical argument. Below is a kernel-checked scratch proof of exactly this statement, with a helper lemma for Step 2. It was elaborated after `import GMT.Ch03.Submission` in the contract scope and uses only the axioms propext, Classical.choice and Quot.sound. When transplanting, rename goodBall to a unique helper name (for example Submission.areaFormula_goodBall_aux) and C2check to Submission.areaFormula_good_chart_pieces.

theorem goodBall {n N p : ℕ} {V : Set (Rn n)} {U : Set (Rn N)} {ψ : Rn n → Rn N}
    {f : Rn N → Rn p}
    (hV : IsOpen V) (hψC : ContDiffOn ℝ 1 ψ V) (hInj : ∀ u ∈ V, Function.Injective (fderiv ℝ ψ u))
    (hU : IsOpen U) (hf : LocallyLipschitzOn U f) {u₀ : Rn n} (hu₀ : u₀ ∈ V) (hx₀ : ψ u₀ ∈ U) :
    ∃ r > 0, Metric.closedBall u₀ r ⊆ V ∧ ∃ K C : ℝ≥0,
      LipschitzOnWith K ψ (Metric.closedBall u₀ r) ∧
      (∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
        dist u v ≤ (C : ℝ) * dist (ψ u) (ψ v)) ∧
      LipschitzOnWith K (f ∘ ψ) (Metric.closedBall u₀ r) := by
  set A := fderiv ℝ ψ u₀ with hA
  obtain ⟨KA, hKA0, hKA⟩ := LinearMap.exists_antilipschitzWith A.toLinearMap
    (LinearMap.ker_eq_bot.mpr (hInj u₀ hu₀))
  have hKA0' : (0 : ℝ) < KA := by exact_mod_cast hKA0
  set m : ℝ := (KA : ℝ)⁻¹ with hm
  have hm0 : 0 < m := inv_pos.mpr hKA0'
  have hAlow : ∀ w : Rn n, m * ‖w‖ ≤ ‖A w‖ := by
    intro w
    have h1 : dist w 0 ≤ KA * dist (A.toLinearMap w) (A.toLinearMap 0) := hKA.le_mul_dist w 0
    rw [map_zero, dist_zero_right, dist_zero_right] at h1
    have h2 : ‖w‖ ≤ KA * ‖A w‖ := h1
    rw [hm, inv_mul_le_iff₀ hKA0']
    exact h2
  have hcont : ContinuousOn (fun z ↦ fderiv ℝ ψ z) V :=
    hψC.continuousOn_fderiv_of_isOpen hV le_rfl
  have hcontAt : ContinuousAt (fun z ↦ fderiv ℝ ψ z) u₀ := hcont.continuousAt (hV.mem_nhds hu₀)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.mp hcontAt (m / 2) (half_pos hm0)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.isOpen_iff.mp hV u₀ hu₀
  obtain ⟨Lf, t, ht, hLf⟩ := hf hx₀
  rw [hU.nhdsWithin_eq hx₀] at ht
  obtain ⟨s, hs, hst⟩ := Metric.mem_nhds_iff.mp ht
  have hψcontAt : ContinuousAt ψ u₀ := hψC.continuousOn.continuousAt (hV.mem_nhds hu₀)
  obtain ⟨δ₃, hδ₃, hδ₃'⟩ := Metric.continuousAt_iff.mp hψcontAt s hs
  set r := min (min δ₁ δ₂) δ₃ / 2 with hr
  have hmin0 : 0 < min (min δ₁ δ₂) δ₃ := lt_min (lt_min hδ₁ hδ₂) hδ₃
  have hr0 : 0 < r := by rw [hr]; linarith
  have hrmin : r < min (min δ₁ δ₂) δ₃ := by rw [hr]; linarith
  have hrlt : ∀ u ∈ Metric.closedBall u₀ r,
      dist u u₀ < δ₁ ∧ dist u u₀ < δ₂ ∧ dist u u₀ < δ₃ := by
    intro u hu
    have hu' : dist u u₀ < min (min δ₁ δ₂) δ₃ :=
      lt_of_le_of_lt (Metric.mem_closedBall.mp hu) hrmin
    simp only [lt_min_iff] at hu'
    exact ⟨hu'.1.1, hu'.1.2, hu'.2⟩
  have hBV : Metric.closedBall u₀ r ⊆ V := fun u hu ↦ hδ₂' (Metric.mem_ball.mpr (hrlt u hu).2.1)
  have hdiffB : ∀ z ∈ Metric.closedBall u₀ r, DifferentiableAt ℝ ψ z := fun z hz ↦
    ((hψC.differentiableOn one_ne_zero) z (hBV hz)).differentiableAt (hV.mem_nhds (hBV hz))
  have hMV : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
      ‖(ψ u - A u) - (ψ v - A v)‖ ≤ m / 2 * ‖u - v‖ := by
    intro u hu v hv
    have hg : ∀ z ∈ Metric.closedBall u₀ r, DifferentiableAt ℝ (fun z ↦ ψ z - A z) z :=
      fun z hz ↦ (hdiffB z hz).sub A.differentiableAt
    have hbound : ∀ z ∈ Metric.closedBall u₀ r, ‖fderiv ℝ (fun z ↦ ψ z - A z) z‖ ≤ m / 2 := by
      intro z hz
      rw [fderiv_fun_sub (hdiffB z hz) A.differentiableAt, A.fderiv, ← dist_eq_norm]
      exact (hδ₁' (hrlt z hz).1).le
    exact Convex.norm_image_sub_le_of_norm_fderiv_le hg hbound (convex_closedBall u₀ r) hv hu
  have hupper : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
      dist (ψ u) (ψ v) ≤ (‖A‖ + m / 2) * dist u v := by
    intro u hu v hv
    rw [dist_eq_norm, dist_eq_norm]
    have h1 := hMV u hu v hv
    have h2 : ‖A (u - v)‖ ≤ ‖A‖ * ‖u - v‖ := A.le_opNorm _
    have h3 : ψ u - ψ v = ((ψ u - A u) - (ψ v - A v)) + A (u - v) := by rw [map_sub]; abel
    calc ‖ψ u - ψ v‖ = ‖((ψ u - A u) - (ψ v - A v)) + A (u - v)‖ := by rw [← h3]
      _ ≤ ‖(ψ u - A u) - (ψ v - A v)‖ + ‖A (u - v)‖ := norm_add_le _ _
      _ ≤ m / 2 * ‖u - v‖ + ‖A‖ * ‖u - v‖ := add_le_add h1 h2
      _ = (‖A‖ + m / 2) * ‖u - v‖ := by ring
  have hlower : ∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
      dist u v ≤ ((2 * KA : ℝ≥0) : ℝ) * dist (ψ u) (ψ v) := by
    intro u hu v hv
    rw [dist_eq_norm, dist_eq_norm]
    have h1 := hMV u hu v hv
    have h2 := hAlow (u - v)
    have h3 : A (u - v) = (ψ u - ψ v) - ((ψ u - A u) - (ψ v - A v)) := by rw [map_sub]; abel
    have h4 : ‖A (u - v)‖ ≤ ‖ψ u - ψ v‖ + m / 2 * ‖u - v‖ := by
      rw [h3]; exact (norm_sub_le _ _).trans (add_le_add le_rfl h1)
    have h5 : m / 2 * ‖u - v‖ ≤ ‖ψ u - ψ v‖ := by linarith
    have hKAeq : (KA : ℝ) * m = 1 := by rw [hm]; exact mul_inv_cancel₀ hKA0'.ne'
    push_cast
    calc ‖u - v‖ = (2 * KA) * (m / 2 * ‖u - v‖) := by
          have : (2 * (KA : ℝ)) * (m / 2 * ‖u - v‖) = ((KA : ℝ) * m) * ‖u - v‖ := by ring
          rw [this, hKAeq, one_mul]
      _ ≤ (2 * KA) * ‖ψ u - ψ v‖ := mul_le_mul_of_nonneg_left h5 (by positivity)
  set K0 : ℝ≥0 := ⟨‖A‖ + m / 2, by positivity⟩ with hK0
  have hK0r : (K0 : ℝ) = ‖A‖ + m / 2 := rfl
  refine ⟨r, hr0, hBV, K0 + Lf * K0, 2 * KA, ?_, hlower, ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_
    calc dist (ψ u) (ψ v) ≤ (‖A‖ + m / 2) * dist u v := hupper u hu v hv
      _ ≤ ((K0 + Lf * K0 : ℝ≥0) : ℝ) * dist u v := by
        push_cast
        rw [hK0r]
        have h0 : 0 ≤ (Lf : ℝ) * (‖A‖ + m / 2) := by positivity
        exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
  · refine LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_
    have hψu : ψ u ∈ t := hst (Metric.mem_ball.mpr (hδ₃' (hrlt u hu).2.2))
    have hψv : ψ v ∈ t := hst (Metric.mem_ball.mpr (hδ₃' (hrlt v hv).2.2))
    calc dist (f (ψ u)) (f (ψ v)) ≤ Lf * dist (ψ u) (ψ v) := hLf.dist_le_mul _ hψu _ hψv
      _ ≤ Lf * ((‖A‖ + m / 2) * dist u v) := by gcongr; exact hupper u hu v hv
      _ ≤ ((K0 + Lf * K0 : ℝ≥0) : ℝ) * dist u v := by
        push_cast
        rw [hK0r]
        have h0 : 0 ≤ (‖A‖ + m / 2) * dist u v := by positivity
        have h1 : (‖A‖ + m / 2 + ↑Lf * (‖A‖ + m / 2)) * dist u v =
            (‖A‖ + m / 2) * dist u v + ↑Lf * ((‖A‖ + m / 2) * dist u v) := by ring
        rw [h1]
        linarith

theorem C2check : ∀ (n N p : ℕ) (M U N₀ : Set (Rn N)) (S : ℕ → Set (Rn N)) (f : Rn N → Rn p), IsOpen U → M ⊆ U → LocallyLipschitzOn U f → (∀ j, IsC1Submanifold n (S j)) → M ⊆ N₀ ∪ ⋃ j, S j → ∃ (V D : ℕ → Set (Rn n)) (ψ : ℕ → Rn n → Rn N) (K C : ℕ → ℝ≥0), (∀ α, IsOpen (V α) ∧ ContDiffOn ℝ 1 (ψ α) (V α) ∧ (∀ u ∈ V α, Function.Injective (fderiv ℝ (ψ α) u)) ∧ IsCompact (D α) ∧ D α ⊆ V α ∧ LipschitzOnWith (K α) (ψ α) (D α) ∧ (∀ u ∈ D α, ∀ v ∈ D α, dist u v ≤ (C α : ℝ) * dist (ψ α u) (ψ α v)) ∧ LipschitzOnWith (K α) (f ∘ ψ α) (D α)) ∧ M ⊆ N₀ ∪ ⋃ α, ψ α '' D α := by
  intro n N p M U N₀ S f hU hMU hf hS hcov
  classical
  choose! Vc Wc ψc hVc hWc hyW hψC hInjOn hImg hProper hDer using hS
  choose T hTS hTc hTU using fun j ↦
    TopologicalSpace.isOpen_biUnion_countable (S j) (Wc j) (fun y hy ↦ hWc j y hy)
  have hgood : ∀ j, ∀ y ∈ S j, ∀ u₀ ∈ Vc j y ∩ ψc j y ⁻¹' U, ∃ r > 0,
      Metric.closedBall u₀ r ⊆ Vc j y ∧ ∃ K C : ℝ≥0,
        LipschitzOnWith K (ψc j y) (Metric.closedBall u₀ r) ∧
        (∀ u ∈ Metric.closedBall u₀ r, ∀ v ∈ Metric.closedBall u₀ r,
          dist u v ≤ (C : ℝ) * dist (ψc j y u) (ψc j y v)) ∧
        LipschitzOnWith K (f ∘ ψc j y) (Metric.closedBall u₀ r) := fun j y hy u₀ hu₀ ↦
    goodBall (hVc j y hy) (hψC j y hy) (hDer j y hy) hU hf hu₀.1 hu₀.2
  choose! r hr hrV Kb Cb hKb hCb hfKb using hgood
  choose Q hQO hQc hQU using fun j y ↦
    TopologicalSpace.isOpen_biUnion_countable (Vc j y ∩ ψc j y ⁻¹' U)
      (fun u₀ ↦ Metric.ball u₀ (r j y u₀)) (fun _ _ ↦ Metric.isOpen_ball)
  set I : Set (ℕ × Rn N × Rn n) := ⋃ j, ⋃ y ∈ T j, (fun u ↦ (j, y, u)) '' Q j y with hIdef
  have hIc : I.Countable :=
    Set.countable_iUnion fun j ↦ (hTc j).biUnion fun y _ ↦ (hQc j y).image _
  have hImem : ∀ π ∈ I, π.2.1 ∈ T π.1 ∧ π.2.2 ∈ Q π.1 π.2.1 := by
    intro π hπ
    simp only [hIdef, mem_iUnion, mem_image] at hπ
    obtain ⟨j, y, hy, u, hu, rfl⟩ := hπ
    exact ⟨hy, hu⟩
  have hpiece : ∀ π ∈ I, IsOpen (Vc π.1 π.2.1) ∧ ContDiffOn ℝ 1 (ψc π.1 π.2.1) (Vc π.1 π.2.1) ∧
      (∀ u ∈ Vc π.1 π.2.1, Function.Injective (fderiv ℝ (ψc π.1 π.2.1) u)) ∧
      IsCompact (Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2)) ∧
      Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2) ⊆ Vc π.1 π.2.1 ∧
      LipschitzOnWith (Kb π.1 π.2.1 π.2.2) (ψc π.1 π.2.1)
        (Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2)) ∧
      (∀ u ∈ Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2),
        ∀ v ∈ Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2),
          dist u v ≤ (Cb π.1 π.2.1 π.2.2 : ℝ) * dist (ψc π.1 π.2.1 u) (ψc π.1 π.2.1 v)) ∧
      LipschitzOnWith (Kb π.1 π.2.1 π.2.2) (f ∘ ψc π.1 π.2.1)
        (Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2)) := by
    intro π hπ
    obtain ⟨hyT, huQ⟩ := hImem π hπ
    have hy : π.2.1 ∈ S π.1 := hTS π.1 hyT
    have hu : π.2.2 ∈ Vc π.1 π.2.1 ∩ ψc π.1 π.2.1 ⁻¹' U := hQO π.1 π.2.1 huQ
    exact ⟨hVc _ _ hy, hψC _ _ hy, hDer _ _ hy, isCompact_closedBall _ _, hrV _ _ hy _ hu,
      hKb _ _ hy _ hu, hCb _ _ hy _ hu, hfKb _ _ hy _ hu⟩
  have hcovI : ∀ x ∈ M, x ∉ N₀ → ∃ π ∈ I,
      x ∈ ψc π.1 π.2.1 '' Metric.closedBall π.2.2 (r π.1 π.2.1 π.2.2) := by
    intro x hxM hxN
    rcases hcov hxM with hx0 | hx1
    · exact absurd hx0 hxN
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx1
    have hxW : x ∈ ⋃ y ∈ T j, Wc j y := by
      rw [hTU j]; exact mem_biUnion hxj (hyW j x hxj)
    obtain ⟨y, hyT, hxWy⟩ := mem_iUnion₂.mp hxW
    have hy : y ∈ S j := hTS j hyT
    have hxim : x ∈ ψc j y '' Vc j y := by rw [hImg j y hy]; exact ⟨hxWy, hxj⟩
    obtain ⟨u, huV, rfl⟩ := hxim
    have huO : u ∈ Vc j y ∩ ψc j y ⁻¹' U := ⟨huV, hMU hxM⟩
    have hu' : u ∈ ⋃ u₀ ∈ Q j y, Metric.ball u₀ (r j y u₀) := by
      rw [hQU j y]; exact mem_biUnion huO (Metric.mem_ball_self (hr j y hy u huO))
    obtain ⟨u₀, hu₀Q, huB⟩ := mem_iUnion₂.mp hu'
    refine ⟨(j, y, u₀), ?_, u, Metric.ball_subset_closedBall huB, rfl⟩
    simp only [hIdef, mem_iUnion, mem_image]
    exact ⟨j, y, hyT, u₀, hu₀Q, rfl⟩
  by_cases hIne : I.Nonempty
  · obtain ⟨e, he⟩ := hIc.exists_eq_range hIne
    have heI : ∀ α, e α ∈ I := fun α ↦ by rw [he]; exact mem_range_self α
    refine ⟨fun α ↦ Vc (e α).1 (e α).2.1,
      fun α ↦ Metric.closedBall (e α).2.2 (r (e α).1 (e α).2.1 (e α).2.2),
      fun α ↦ ψc (e α).1 (e α).2.1, fun α ↦ Kb (e α).1 (e α).2.1 (e α).2.2,
      fun α ↦ Cb (e α).1 (e α).2.1 (e α).2.2, fun α ↦ hpiece (e α) (heI α), ?_⟩
    intro x hxM
    by_cases hxN : x ∈ N₀
    · exact Or.inl hxN
    · obtain ⟨π, hπI, hxπ⟩ := hcovI x hxM hxN
      rw [he] at hπI
      obtain ⟨α, rfl⟩ := hπI
      exact Or.inr (mem_iUnion.mpr ⟨α, hxπ⟩)
  · refine ⟨fun _ ↦ ∅, fun _ ↦ ∅, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, fun α ↦ ?_, ?_⟩
    · simp
    · intro x hxM
      by_cases hxN : x ∈ N₀
      · exact Or.inl hxN
      · obtain ⟨π, hπI, -⟩ := hcovI x hxM hxN
        exact absurd ⟨π, hπI⟩ hIne

## Key steps

1. Lindelöf: each S_j is a countable union of chart images ψ_c(V_c), with Dψ_c injective on V_c.
2. At u₀ ∈ V_c with ψ_c(u₀) ∈ U: injectivity of Dψ_c(u₀), continuity of Dψ_c and the mean value inequality give a closed ball on which ψ_c is bi-Lipschitz. Local Lipschitzness of f on the open U makes f∘ψ_c Lipschitz there.
3. Lindelöf in ℝⁿ: countably many such balls cover the open set V_c ∩ ψ_c⁻¹(U).
4. Enumerate the countable family of pieces by ℕ, using trivial empty pieces if the family is empty. Closed balls are compact.
5. Every x ∈ M ∖ N₀ is ψ_c(u) with u in one of the chosen balls, so M ⊆ N₀ ∪ ⋃_α ψ_α(D_α).

## Reference use

### local-project

Queries:
- `rg -n "^def AreaFormula|^def IsC1Submanifold|^noncomputable def approxTangentPlane|^noncomputable def tangentialDifferential|^noncomputable def areaJacobian|^def HasTangentialDifferentialAt|^def IsPositiveLocallyIntegrableWeight|^abbrev Rn" project/GMT/Ch03/Contract.lean`
- `rg -n "theorem normDet_comp|theorem normDet_codRestrict|theorem normDet_ne_zero_tfae|theorem normDet_nonneg|normDet_sq" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n "theorem lintegral_iUnion₀|theorem lintegral_tsum|theorem lintegral_indicator₀" mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/`
- `rg -n "theorem isOpen_iUnion_countable|theorem isOpen_biUnion_countable" mathlib/Mathlib/Topology/Bases.lean`
- `rg -n "theorem HasLineDerivAt.unique" mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `rg -n "theorem LinearMap.exists_antilipschitzWith" mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n "theorem approximates_deriv_on_nhds|protected theorem lipschitzWith" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/`
- `rg -n "theorem ContinuousOn.measurable_piecewise" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `rg -n "theorem measurable_fderiv |theorem measurableSet_of_differentiableAt " mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `rg -n "exists_measurable_subset_ae_eq" mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `rg -n "lemma tsum_set_one|protected theorem tsum_biUnion" mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `rg -n "theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "^def LocallyLipschitzOn" mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `rg -n -l "areaFormula_|AreaFormula" mathlib/Mathlib  (no match)`
- `rg -n -i -l "coarea|area_formula" mathlib/Mathlib  (no match)`
- `grep -n "weighted_area_formula_lipschitzOn_fiberSum|aemeasurable_weightedAreaFiberSum_lipschitzOn|ae_eq_of_hasFDerivWithinAt|def areaJacobianWithin|def weightedAreaFiberSum|def areaFiber|theorem continuous_normDet|euclideanHausdorffMeasure_image_le_of_lipschitzOn|HasWeightedApproximateTangentSpaceAt.unique" in the pinned simongmt package lake-packages-25730c7c/simongmt/Poincare/SimonGMT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`

Snapshot: project d09bc8a, Mathlib 25730c7c, plus the pinned simongmt package (2b36630). The contract definitions used by the children are in Contract.lean (Rn line 56, IsC1Submanifold 68, approxTangentPlane 84, HasTangentialDifferentialAt 92, tangentialDifferential 97, areaJacobian 102, AreaFormula 218).

Found and cited from Mathlib:
- NormDet.lean: LinearMap.normDet_comp (324), normDet_comp_of_finrank_eq (348), normDet_codRestrict (365), normDet_nonneg, normDet_ne_zero_tfae / normDet_eq_zero_iff_ker_ne_bot.
- lintegral_indicator₀ (Lebesgue/Basic.lean 518), lintegral_iUnion₀ (592), lintegral_tsum (Lebesgue/Add.lean 362).
- TopologicalSpace.isOpen_biUnion_countable (Bases.lean 942); HasLineDerivAt.unique (LineDeriv/Basic.lean 156).
- LinearMap.exists_antilipschitzWith (FiniteDimension.lean 231); HasStrictFDerivAt.approximates_deriv_on_nhds (InverseFunctionTheorem/FDeriv.lean 76).
- ContinuousOn.measurable_piecewise (BorelSpace/Basic.lean 523); measurableSet_of_differentiableAt and measurable_fderiv (FDeriv/Measurable.lean 372, 378); NullMeasurableSet.exists_measurable_subset_ae_eq (NullMeasurable.lean 214).
- ENNReal.tsum_set_one (636) and ENNReal.tsum_biUnion (94) in InfiniteSum/ENNReal.lean; EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean 187); LocallyLipschitzOn (EMetricSpace/Lipschitz.lean 72).

Found and cited from SimonGMT:
- AreaDomain.lean: weighted_area_formula_lipschitzOn_fiberSum, aemeasurable_weightedAreaFiberSum_lipschitzOn, ae_eq_of_hasFDerivWithinAt, areaJacobianWithin (= normDet ∘ fderivWithin).
- AreaMultiplicity.lean: areaFiber, weightedAreaFiberSum.
- continuous_normDet (AreaApproximation.lean 28); euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean 216); HasWeightedApproximateTangentSpaceAt.unique (Chapter03/Rectifiable.lean 345).

No match: rg finds no AreaFormula or areaFormula_ declaration and no area or coarea formula in the snapshot's Mathlib. The per-piece formula therefore uses SimonGMT's area formulas for Lipschitz maps on Euclidean domains (AreaDomain.lean). That file is not in the import closure of GMT.Ch03.Submission, so Submission.lean must add `import Poincare.SimonGMT.Chapter02.AreaDomain`. Its oleans are present, and the comparator does not freeze Submission's imports.

Checks run against this toolchain:
- All five child statements elaborate after `import GMT.Ch03.Submission`.
- A scratch proof of AreaFormula from the five children plus the two siblings compiles.
- Scratch proofs of all five children compile with the standard axioms only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
