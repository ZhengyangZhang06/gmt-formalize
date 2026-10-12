<!-- theorem-id: gmt-ch03/root.area_formula-a1.chart_piece_formula-a1 -->

## Theorem `Submission.areaFormula_on_chart_piece`

Let n, N, p ∈ ℕ, ψ : ℝⁿ → ℝ^N, f : ℝ^N → ℝ^p, D ⊆ ℝⁿ, K, C ∈ ℝ≥0, J : ℝ^N → ℝ, S ⊆ ℝ^N and h : ℝ^N → [0, ∞]. Assume:
- D is compact;
- ψ is differentiable at every u ∈ D, and Dψ(u) is injective for u ∈ D;
- ψ is K-Lipschitz on D, and |u − v| ≤ C|ψ(u) − ψ(v)| for u, v ∈ D;
- f∘ψ is K-Lipschitz on D;
- S ⊆ ψ(D), and S is Hⁿ-measurable (null-measurable for μHE[n] on ℝ^N);
- for Lⁿ-a.e. u ∈ D with ψ(u) ∈ S, f∘ψ is differentiable at u and J(ψ(u))·normDet(Dψ(u)) = normDet(D(f∘ψ)(u));
- h is Hⁿ⌞S-a.e.-measurable.

Then ∫_S h·ofReal(J) dHⁿ = ∫_{ℝ^p} Σ_{x∈S∩f⁻¹{y}} h(x) dHⁿ(y), and y ↦ Σ_{x∈S∩f⁻¹{y}} h(x) is AEMeasurable for Hⁿ on ℝ^p.

Node: `root.area_formula-a1.chart_piece_formula-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/27

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.areaFormula_on_chart_piece`

```lean
∀ (n N p : ℕ) (ψ : Rn n → Rn N) (f : Rn N → Rn p) (D : Set (Rn n)) (K C : ℝ≥0) (J : Rn N → ℝ) (S : Set (Rn N)) (h : Rn N → ℝ≥0∞), IsCompact D → (∀ u ∈ D, DifferentiableAt ℝ ψ u) → (∀ u ∈ D, Function.Injective (fderiv ℝ ψ u)) → LipschitzOnWith K ψ D → (∀ u ∈ D, ∀ v ∈ D, dist u v ≤ (C : ℝ) * dist (ψ u) (ψ v)) → LipschitzOnWith K (f ∘ ψ) D → S ⊆ ψ '' D → NullMeasurableSet S μHE[n] → (∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ D → ψ u ∈ S → DifferentiableAt ℝ (f ∘ ψ) u ∧ J (ψ u) * (fderiv ℝ ψ u).toLinearMap.normDet = (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet) → AEMeasurable h ((μHE[n] : Measure (Rn N)).restrict S) → (∫⁻ x in S, h x * ENNReal.ofReal (J x) ∂μHE[n] = ∫⁻ y, ∑' x : ↥(S ∩ f ⁻¹' {y}), h x ∂μHE[n]) ∧ AEMeasurable (fun y ↦ ∑' x : ↥(S ∩ f ⁻¹' {y}), h x) (μHE[n] : Measure (Rn p))
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
- Child DAG node: `root.area_formula-a1.chart_piece_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 3-5 and 7 of the parent proof, restricted to one chart piece A_α = ψ_α(B_α). This is Simon Ch. 3, proof of (2.4)-(2.5) (chapter-03.txt lines 370-401) on one piece, along the route of lines 370-371 (“In view of 4.11 and the area formula for Lipschitz maps from domains in ℝⁿ …”). It combines:
- the injective (weighted) area formula, Simon Ch. 2 (3.2)/(4.13), for the chart ψ;
- the Jacobian identity, Ch. 2 (4.11), which is a hypothesis here;
- the Lipschitz area formula with multiplicity and weights, Simon Ch. 2 (3.4)-(3.5) (chapter-02.txt lines 757-796), for f∘ψ.

Library, SimonGMT:
- Chapter02/AreaDomain.lean: weighted_area_formula_lipschitzOn_fiberSum, aemeasurable_weightedAreaFiberSum_lipschitzOn, ae_eq_of_hasFDerivWithinAt, and areaJacobianWithin g s u = normDet(fderivWithin ℝ g s u);
- Chapter02/AreaMultiplicity.lean: weightedAreaFiberSum and areaFiber;
- continuous_normDet (Chapter02/AreaApproximation.lean);
- euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean).

Library, Mathlib: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, finrank_euclideanSpace_fin, measurable_fderiv, measurableSet_of_differentiableAt, ContinuousOn.measurable_piecewise, NullMeasurableSet.exists_measurable_subset_ae_eq, lintegral_indicator₀, ENNReal.ofReal_mul, LinearMap.normDet_nonneg, LinearMap.normDet_eq_zero_iff_ker_ne_bot, Equiv.tsum_eq.

Notation.
- ℝ^d = Rn d.
- Hⁿ = μHE[n] on ℝ^N and on ℝ^p.
- Lⁿ = volume on ℝⁿ; μHE[n] = Lⁿ on ℝⁿ (EuclideanSpace.euclideanHausdorffMeasure_eq_volume), and μHE[finrank ℝ ℝⁿ] = μHE[n].
- g := f∘ψ.
- For a map k, Jk(u) := normDet(fderiv ℝ k u) ≥ 0.
- ofReal := ENNReal.ofReal.

Hypotheses:
- (H1) D is compact.
- (H2) ψ is differentiable at every u ∈ D.
- (H3) Dψ(u) is injective for u ∈ D.
- (H4) ψ is K-Lipschitz on D.
- (H5) |u − v| ≤ C|ψ(u) − ψ(v)| for u, v ∈ D.
- (H6) g is K-Lipschitz on D.
- (H7) S ⊆ ψ(D).
- (H8) S is μHE[n]-null-measurable.
- (H9) For Lⁿ-a.e. u with u ∈ D and ψ(u) ∈ S, g is differentiable at u and J(ψ(u))·Jψ(u) = Jg(u).
- (H10) h is AEMeasurable for Hⁿ⌞S.

Put B := D ∩ ψ⁻¹(S). Conclusions:
- (C1) ∫_S h·ofReal(J) dHⁿ = ∫_{ℝ^p} Σ_{x∈S∩f⁻¹{y}} h(x) dHⁿ(y).
- (C2) y ↦ Σ_{x∈S∩f⁻¹{y}} h(x) is AEMeasurable for Hⁿ on ℝ^p.

No sign or measurability assumption on J is needed.

Proof.
1. Injectivity and the inverse chart. By (H5), ψ(u) = ψ(v) with u, v ∈ D gives |u − v| ≤ 0, so ψ is injective on D. Let φ := invFunOn ψ D. Then φ(ψ(u)) = u for u ∈ D, and φ(x) ∈ D, ψ(φ(x)) = x for x ∈ ψ(D). By (H5), φ is C-Lipschitz on ψ(D). For every E ⊆ ψ(D) we have D ∩ ψ⁻¹(E) = φ(E). Hence, by the Lipschitz image estimate for arbitrary sets, Lⁿ(D ∩ ψ⁻¹(E)) = Hⁿ(φ(E)) ≤ Cⁿ·Hⁿ(E); in particular Hⁿ(E) = 0 implies Lⁿ(D ∩ ψ⁻¹(E)) = 0. Also ψ(B) = S by (H7), so ψ restricts to a bijection B → S.
2. B is Lⁿ-null-measurable. D is compact, hence closed and Borel. By (H8), choose a Borel S′ ⊆ S with Hⁿ(S ∖ S′) = 0. ψ is continuous on the closed set D (H4), so ψ̃ := D.piecewise ψ 0 is Borel (ContinuousOn.measurable_piecewise), and D ∩ ψ⁻¹(S′) = D ∩ ψ̃⁻¹(S′) is Borel. D ∩ ψ⁻¹(S ∖ S′) is Lⁿ-null by Step 1, since S ∖ S′ ⊆ ψ(D). So B = (D ∩ ψ⁻¹(S′)) ∪ (D ∩ ψ⁻¹(S ∖ S′)) is Lⁿ-null-measurable. ψ and g are K-Lipschitz on B ⊆ D.
3. Measurability on B.
 (a) By (H10) there is a Borel h′ with h = h′ Hⁿ⌞S-a.e. Then Z₀ := S ∩ {h ≠ h′} is Hⁿ-null, so D ∩ ψ⁻¹(Z₀) is Lⁿ-null (Step 1). For u ∈ B outside this set, h(ψ(u)) = h′(ψ̃(u)), and h′∘ψ̃ is Borel. So u ↦ h(ψ(u)) is AEMeasurable for Lⁿ⌞B.
 (b) For u ∈ D, Jψ(u) > 0 by (H3), since normDet ≥ 0 and normDet = 0 iff the kernel is nontrivial. The maps u ↦ Jψ(u) and u ↦ Jg(u) are Borel: measurable_fderiv composed with the continuous map L ↦ normDet(L) (SimonGMT continuous_normDet). By (H9), J(ψ(u)) = Jg(u)/Jψ(u) for Lⁿ-a.e. u ∈ B. So u ↦ J(ψ(u)) is AEMeasurable for Lⁿ⌞B, and so is w(u) := h(ψ(u))·ofReal(J(ψ(u))).
4. Jacobians within B.
 - Choose a Borel t₁ ⊆ B with Lⁿ(B ∖ t₁) = 0 (NullMeasurableSet.exists_measurable_subset_ae_eq). For u ∈ t₁ ⊆ D, ψ is differentiable at u (H2). So both Dψ(u) (HasFDerivAt.hasFDerivWithinAt) and fderivWithin ℝ ψ B u (DifferentiableWithinAt.hasFDerivWithinAt, then restriction from B to t₁ ⊆ B) are derivatives of ψ within t₁ at u.
 - Within-derivatives along a Borel set agree Lⁿ-a.e. on it (SimonGMT ae_eq_of_hasFDerivWithinAt). So fderivWithin ℝ ψ B = Dψ Lⁿ-a.e. on t₁, hence Lⁿ-a.e. on B, since Lⁿ⌞B = Lⁿ⌞t₁.
 - For g: B_g := B ∩ {u : g differentiable at u} is null-measurable (measurableSet_of_differentiableAt), and Lⁿ(B ∖ B_g) = 0 by (H9). Choose a Borel t₂ ⊆ B_g with Lⁿ(B_g ∖ t₂) = 0 and argue as above to get fderivWithin ℝ g B = Dg Lⁿ-a.e. on B.
 - Hence areaJacobianWithin ψ B u = Jψ(u) and areaJacobianWithin g B u = Jg(u) for Lⁿ-a.e. u ∈ B.
5. Injective area formula for ψ on B. SimonGMT weighted_area_formula_lipschitzOn_fiberSum for ψ on B (Step 2), with weight w (Step 3), gives
 ∫_{ℝ^N} Σ_{u∈B, ψ(u)=x} w(u) dHⁿ(x) = ∫_B ofReal(areaJacobianWithin ψ B u)·w(u) dLⁿ(u).
 By Step 1, the fibre {u ∈ B : ψ(u) = x} is {φ(x)} if x ∈ S and empty if x ∉ S. So the left integrand is 1_S(x)·h(x)·ofReal(J(x)), and by (H8) and lintegral_indicator₀ the left side is ∫_S h·ofReal(J) dHⁿ. By Step 4 the right side is ∫_B ofReal(Jψ(u))·h(ψ(u))·ofReal(J(ψ(u))) dLⁿ(u).
6. Jacobian identity. For Lⁿ-a.e. u ∈ B, using (H9), Jψ(u) ≥ 0 and ENNReal.ofReal_mul:
 ofReal(Jψ(u))·ofReal(J(ψ(u))) = ofReal(Jψ(u)·J(ψ(u))) = ofReal(Jg(u)).
 With Step 4: ∫_S h·ofReal(J) dHⁿ = ∫_B ofReal(areaJacobianWithin g B u)·h(ψ(u)) dLⁿ(u).
7. Area formula for g on B. SimonGMT weighted_area_formula_lipschitzOn_fiberSum for g on B ((H6), Step 2), with weight h∘ψ (Step 3(a)), gives
 ∫_B ofReal(areaJacobianWithin g B u)·h(ψ(u)) dLⁿ(u) = ∫_{ℝ^p} Σ_{u∈B, g(u)=y} h(ψ(u)) dHⁿ(y).
 SimonGMT aemeasurable_weightedAreaFiberSum_lipschitzOn, under the same hypotheses, shows that y ↦ Σ_{u∈B, g(u)=y} h(ψ(u)) is AEMeasurable for Hⁿ on ℝ^p.
8. Reindexing fibres. For each y, u ↦ ψ(u) is a bijection from {u ∈ B : f(ψ(u)) = y} onto S ∩ f⁻¹{y}:
 - it is injective by Step 1;
 - it maps into S ∩ f⁻¹{y} by the definition of B;
 - it is onto, because each x ∈ S ∩ f⁻¹{y} is ψ(u) with u := φ(x) ∈ D, and then u ∈ B and f(ψ(u)) = y.
 Reindexing the [0,∞]-valued sum along this bijection (Equiv.tsum_eq) gives Σ_{u∈B, g(u)=y} h(ψ(u)) = Σ_{x∈S∩f⁻¹{y}} h(x).
 Steps 5-8 give (C1), and Steps 7-8 give (C2). ∎

Appendix: formalization aid, not part of the mathematical argument. Below is a kernel-checked scratch proof of exactly this statement, using only the axioms propext, Classical.choice and Quot.sound. It needs `import Poincare.SimonGMT.Chapter02.AreaDomain`, which is not in the import closure of GMT.Ch03.Submission: add it to the imports of GMT/Ch03/Submission.lean. The import is in the pinned simongmt package, its oleans are present, and Submission imports are not frozen. Put `open Poincare.SimonGMT.Chapter02 (weighted_area_formula_lipschitzOn_fiberSum aemeasurable_weightedAreaFiberSum_lipschitzOn ae_eq_of_hasFDerivWithinAt areaJacobianWithin weightedAreaFiberSum areaFiber continuous_normDet euclideanHausdorffMeasure_image_le_of_lipschitzOn) in` immediately before the theorem, and rename C4check to Submission.areaFormula_on_chart_piece. Two Lean pitfalls: (1) tsum_eq_single over areaFiber fails instance synthesis, so sum over the underlying subtype {x // x ∈ B ∧ ψ x = y}; (2) rewrite μHE[finrank ℝ (Rn n)] with finrank_euclideanSpace_fin.

theorem C4check : ∀ (n N p : ℕ) (ψ : Rn n → Rn N) (f : Rn N → Rn p) (D : Set (Rn n)) (K C : ℝ≥0) (J : Rn N → ℝ) (S : Set (Rn N)) (h : Rn N → ℝ≥0∞), IsCompact D → (∀ u ∈ D, DifferentiableAt ℝ ψ u) → (∀ u ∈ D, Function.Injective (fderiv ℝ ψ u)) → LipschitzOnWith K ψ D → (∀ u ∈ D, ∀ v ∈ D, dist u v ≤ (C : ℝ) * dist (ψ u) (ψ v)) → LipschitzOnWith K (f ∘ ψ) D → S ⊆ ψ '' D → NullMeasurableSet S μHE[n] → (∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ D → ψ u ∈ S → DifferentiableAt ℝ (f ∘ ψ) u ∧ J (ψ u) * (fderiv ℝ ψ u).toLinearMap.normDet = (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet) → AEMeasurable h ((μHE[n] : Measure (Rn N)).restrict S) → (∫⁻ x in S, h x * ENNReal.ofReal (J x) ∂μHE[n] = ∫⁻ y, ∑' x : ↥(S ∩ f ⁻¹' {y}), h x ∂μHE[n]) ∧ AEMeasurable (fun y ↦ ∑' x : ↥(S ∩ f ⁻¹' {y}), h x) (μHE[n] : Measure (Rn p)) := by
  intro n N p ψ f D K C J S h hD hdiff hinj hψL hanti hgL hSD hS hJ hh
  classical
  set B : Set (Rn n) := D ∩ ψ ⁻¹' S with hBdef
  have hBD : B ⊆ D := inter_subset_left
  have hψinj : InjOn ψ D := by
    intro u hu v hv huv
    have := hanti u hu v hv
    rw [huv, dist_self, mul_zero] at this
    exact dist_le_zero.mp this
  have hφL : LipschitzOnWith C (Function.invFunOn ψ D) (ψ '' D) := by
    refine LipschitzOnWith.of_dist_le_mul fun y₁ hy₁ y₂ hy₂ ↦ ?_
    obtain ⟨u₁, hu₁, rfl⟩ := hy₁
    obtain ⟨u₂, hu₂, rfl⟩ := hy₂
    rw [hψinj.leftInvOn_invFunOn hu₁, hψinj.leftInvOn_invFunOn hu₂]
    exact hanti u₁ hu₁ u₂ hu₂
  have hpre : ∀ E ⊆ ψ '' D, D ∩ ψ ⁻¹' E = Function.invFunOn ψ D '' E := by
    intro E hE
    ext u
    constructor
    · rintro ⟨huD, huE⟩
      exact ⟨ψ u, huE, hψinj.leftInvOn_invFunOn huD⟩
    · rintro ⟨y, hyE, rfl⟩
      have hy : ∃ a ∈ D, ψ a = y := hE hyE
      refine ⟨Function.invFunOn_mem hy, ?_⟩
      rw [mem_preimage, Function.invFunOn_eq hy]
      exact hyE
  have hnullpre : ∀ E ⊆ ψ '' D, μHE[n] E = 0 → (volume : Measure (Rn n)) (D ∩ ψ ⁻¹' E) = 0 := by
    intro E hE hE0
    rw [hpre E hE, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    refine le_antisymm ?_ bot_le
    calc μHE[n] (Function.invFunOn ψ D '' E)
        ≤ (C : ℝ≥0∞) ^ n * μHE[n] E :=
          euclideanHausdorffMeasure_image_le_of_lipschitzOn n (hφL.mono hE)
      _ = 0 := by rw [hE0, mul_zero]
  have hDc : IsClosed D := hD.isClosed
  let ψt : Rn n → Rn N := D.piecewise ψ 0
  have hψtm : Measurable ψt :=
    ContinuousOn.measurable_piecewise hψL.continuousOn continuous_zero.continuousOn
      hDc.measurableSet
  have hψt_eq : ∀ u ∈ D, ψt u = ψ u := fun u hu ↦ Set.piecewise_eq_of_mem _ _ _ hu
  obtain ⟨S', hS'S, hS'm, hS'ae⟩ := hS.exists_measurable_subset_ae_eq
  have hSS' : μHE[n] (S \ S') = 0 := (ae_eq_set.mp hS'ae).2
  have hBm : NullMeasurableSet B volume := by
    have h1 : MeasurableSet (D ∩ ψt ⁻¹' S') := hDc.measurableSet.inter (hψtm hS'm)
    have h2 : (volume : Measure (Rn n)) (D ∩ ψ ⁻¹' (S \ S')) = 0 :=
      hnullpre _ (diff_subset.trans hSD) hSS'
    have heq : B = (D ∩ ψt ⁻¹' S') ∪ (D ∩ ψ ⁻¹' (S \ S')) := by
      ext u
      simp only [hBdef, mem_inter_iff, mem_preimage, mem_union, mem_diff]
      constructor
      · rintro ⟨huD, huS⟩
        by_cases hu' : ψ u ∈ S'
        · exact Or.inl ⟨huD, by rw [hψt_eq u huD]; exact hu'⟩
        · exact Or.inr ⟨huD, huS, hu'⟩
      · rintro (⟨huD, hu'⟩ | ⟨huD, huS, -⟩)
        · rw [hψt_eq u huD] at hu'
          exact ⟨huD, hS'S hu'⟩
        · exact ⟨huD, huS⟩
    rw [heq]
    exact h1.nullMeasurableSet.union (NullMeasurableSet.of_null h2)
  have hE0 : μHE[n] (S ∩ {x | h x ≠ hh.mk h x}) = 0 := by
    have := (ae_restrict_iff'₀ hS).mp hh.ae_eq_mk
    rw [ae_iff] at this
    refine measure_mono_null (fun x hx ↦ ?_) this
    simp only [mem_setOf_eq, not_imp]
    exact ⟨hx.1, hx.2⟩
  have hbadh : (volume : Measure (Rn n)) (D ∩ ψ ⁻¹' (S ∩ {x | h x ≠ hh.mk h x})) = 0 :=
    hnullpre _ (inter_subset_left.trans hSD) hE0
  have hhψ : AEMeasurable (fun u ↦ h (ψ u)) (volume.restrict B) := by
    refine ⟨fun u ↦ hh.mk h (ψt u), hh.measurable_mk.comp hψtm, ?_⟩
    refine (ae_restrict_iff'₀ hBm).mpr ?_
    rw [ae_iff]
    refine measure_mono_null (fun u hu ↦ ?_) hbadh
    simp only [mem_setOf_eq, not_imp] at hu
    obtain ⟨⟨huD, huS⟩, hne⟩ := hu
    rw [hψt_eq u huD] at hne
    exact ⟨huD, huS, hne⟩
  have hJψm : Measurable (fun u ↦ (fderiv ℝ ψ u).toLinearMap.normDet) :=
    continuous_normDet.measurable.comp (measurable_fderiv ℝ ψ)
  have hJgm : Measurable (fun u ↦ (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet) :=
    continuous_normDet.measurable.comp (measurable_fderiv ℝ (f ∘ ψ))
  have hJψpos : ∀ u ∈ D, 0 < (fderiv ℝ ψ u).toLinearMap.normDet := by
    intro u hu
    refine lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm ?_)
    intro h0
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h0) (LinearMap.ker_eq_bot.mpr (hinj u hu))
  have hJrel : ∀ᵐ u ∂(volume.restrict B), J (ψ u) * (fderiv ℝ ψ u).toLinearMap.normDet =
      (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet := by
    refine (ae_restrict_iff'₀ hBm).mpr ?_
    filter_upwards [hJ] with u hu huB
    exact (hu huB.1 huB.2).2
  have hJae : ∀ᵐ u ∂(volume.restrict B), (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet /
      (fderiv ℝ ψ u).toLinearMap.normDet = J (ψ u) := by
    have hD' : ∀ᵐ u ∂(volume.restrict B), u ∈ B := ae_restrict_mem₀ hBm
    filter_upwards [hJrel, hD'] with u hu huB
    rw [← hu, mul_div_assoc, div_self (hJψpos u huB.1).ne', mul_one]
  have hJψm' : AEMeasurable (fun u ↦ J (ψ u)) (volume.restrict B) :=
    (hJgm.div hJψm).aemeasurable.congr hJae
  have hw : AEMeasurable (fun u ↦ h (ψ u) * ENNReal.ofReal (J (ψ u))) (volume.restrict B) :=
    hhψ.mul (ENNReal.measurable_ofReal.comp_aemeasurable hJψm')
  obtain ⟨t, htB, htm, htae⟩ := hBm.exists_measurable_subset_ae_eq
  have hfdψ : (fun u ↦ fderivWithin ℝ ψ B u) =ᵐ[volume.restrict B] fderiv ℝ ψ := by
    have := ae_eq_of_hasFDerivWithinAt htm (f := ψ) (L := fun u ↦ fderivWithin ℝ ψ B u)
      (Q := fderiv ℝ ψ)
      (fun u hu ↦ ((hdiff u (htB hu).1).differentiableWithinAt.hasFDerivWithinAt).mono htB)
      (fun u hu ↦ (hdiff u (htB hu).1).hasFDerivAt.hasFDerivWithinAt)
    rwa [Measure.restrict_congr_set htae] at this
  set Bg := B ∩ {u | DifferentiableAt ℝ (f ∘ ψ) u} with hBg
  have hBgm : NullMeasurableSet Bg volume :=
    hBm.inter (measurableSet_of_differentiableAt ℝ (f ∘ ψ)).nullMeasurableSet
  have hBgae : Bg =ᵐ[volume] B := by
    rw [ae_eq_set]
    refine ⟨by rw [diff_eq_empty.mpr inter_subset_left, measure_empty], ?_⟩
    rw [ae_iff] at hJ
    refine measure_mono_null (fun u hu ↦ ?_) hJ
    obtain ⟨⟨huD, huS⟩, hnot⟩ := hu
    intro hcontra
    exact hnot ⟨⟨huD, huS⟩, (hcontra huD huS).1⟩
  obtain ⟨t₂, ht₂B, ht₂m, ht₂ae⟩ := hBgm.exists_measurable_subset_ae_eq
  have hfdg : (fun u ↦ fderivWithin ℝ (f ∘ ψ) B u) =ᵐ[volume.restrict B] fderiv ℝ (f ∘ ψ) := by
    have := ae_eq_of_hasFDerivWithinAt ht₂m (f := f ∘ ψ)
      (L := fun u ↦ fderivWithin ℝ (f ∘ ψ) B u) (Q := fderiv ℝ (f ∘ ψ))
      (fun u hu ↦ ((show DifferentiableAt ℝ (f ∘ ψ) u from (ht₂B hu).2).differentiableWithinAt
        |>.hasFDerivWithinAt).mono (fun v hv ↦ (ht₂B hv).1))
      (fun u hu ↦ (show DifferentiableAt ℝ (f ∘ ψ) u from (ht₂B hu).2).hasFDerivAt.hasFDerivWithinAt)
    rwa [Measure.restrict_congr_set (ht₂ae.trans hBgae)] at this
  have hψB : LipschitzOnWith K ψ B := hψL.mono hBD
  have hgB : LipschitzOnWith K (f ∘ ψ) B := hgL.mono hBD
  have A1 := weighted_area_formula_lipschitzOn_fiberSum hBm hψB hw
  have A2 := weighted_area_formula_lipschitzOn_fiberSum hBm hgB hhψ
  have A3 := aemeasurable_weightedAreaFiberSum_lipschitzOn hBm hgB hhψ
  rw [finrank_euclideanSpace_fin] at A1 A2 A3
  have hfib1 : ∀ y, weightedAreaFiberSum B ψ (fun u ↦ h (ψ u) * ENNReal.ofReal (J (ψ u))) y =
      S.indicator (fun x ↦ h x * ENNReal.ofReal (J x)) y := by
    intro y
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy]
      obtain ⟨u, huD, rfl⟩ := hSD hy
      have huB : u ∈ B := ⟨huD, hy⟩
      show ∑' x : {x // x ∈ B ∧ ψ x = ψ u}, h (ψ x.1) * ENNReal.ofReal (J (ψ x.1)) = _
      refine tsum_eq_single (⟨u, huB, rfl⟩ : {x // x ∈ B ∧ ψ x = ψ u}) fun b hb ↦ ?_
      exact absurd (Subtype.ext (hψinj b.2.1.1 huD b.2.2)) hb
    · rw [indicator_of_notMem hy]
      unfold weightedAreaFiberSum
      exact ENNReal.tsum_eq_zero.mpr fun b ↦
        absurd (show y ∈ S by rw [← b.2.2]; exact b.2.1.2) hy
  have hfib2 : ∀ y, weightedAreaFiberSum B (f ∘ ψ) (fun u ↦ h (ψ u)) y =
      ∑' x : ↥(S ∩ f ⁻¹' {y}), h x := by
    intro y
    have hinj' : Function.Injective (fun b : areaFiber B (f ∘ ψ) y ↦
        (⟨ψ b.1, b.2.1.2, b.2.2⟩ : ↥(S ∩ f ⁻¹' {y}))) := by
      intro b₁ b₂ hb
      exact Subtype.ext (hψinj b₁.2.1.1 b₂.2.1.1 (congrArg Subtype.val hb))
    have hsurj : Function.Surjective (fun b : areaFiber B (f ∘ ψ) y ↦
        (⟨ψ b.1, b.2.1.2, b.2.2⟩ : ↥(S ∩ f ⁻¹' {y}))) := by
      rintro ⟨x, hxS, hxf⟩
      obtain ⟨u, huD, rfl⟩ := hSD hxS
      exact ⟨⟨u, ⟨huD, hxS⟩, hxf⟩, rfl⟩
    unfold weightedAreaFiberSum
    exact (Equiv.ofBijective _ ⟨hinj', hsurj⟩).tsum_eq (fun x : ↥(S ∩ f ⁻¹' {y}) ↦ h x)
  have hfun : (fun y ↦ ∑' x : ↥(S ∩ f ⁻¹' {y}), h x) =
      weightedAreaFiberSum B (f ∘ ψ) (fun u ↦ h (ψ u)) :=
    funext fun y ↦ (hfib2 y).symm
  refine ⟨?_, by rw [hfun]; exact A3⟩
  calc ∫⁻ x in S, h x * ENNReal.ofReal (J x) ∂μHE[n]
      = ∫⁻ y, S.indicator (fun x ↦ h x * ENNReal.ofReal (J x)) y ∂μHE[n] :=
        (lintegral_indicator₀ hS _).symm
    _ = ∫⁻ y, weightedAreaFiberSum B ψ (fun u ↦ h (ψ u) * ENNReal.ofReal (J (ψ u))) y
          ∂μHE[n] := lintegral_congr fun y ↦ (hfib1 y).symm
    _ = ∫⁻ u in B, ENNReal.ofReal (areaJacobianWithin ψ B u) *
          (h (ψ u) * ENNReal.ofReal (J (ψ u))) := A1
    _ = ∫⁻ u in B, ENNReal.ofReal (areaJacobianWithin (f ∘ ψ) B u) * h (ψ u) := by
        apply lintegral_congr_ae
        filter_upwards [hfdψ, hfdg, hJrel] with u h1 h2 h3
        simp only [areaJacobianWithin]
        rw [h1, h2, ← h3, mul_comm (J (ψ u)), ENNReal.ofReal_mul (LinearMap.normDet_nonneg _)]
        ring
    _ = ∫⁻ y, weightedAreaFiberSum B (f ∘ ψ) (fun u ↦ h (ψ u)) y ∂μHE[n] := A2.symm
    _ = ∫⁻ y, ∑' x : ↥(S ∩ f ⁻¹' {y}), h x ∂μHE[n] := lintegral_congr hfib2

## Key steps

1. ψ is injective on D with a C-Lipschitz inverse on ψ(D), so Hⁿ-null subsets of ψ(D) pull back to Lⁿ-null subsets of D.
2. B := D ∩ ψ⁻¹(S) is Lⁿ-null-measurable, and ψ : B → S is a bijection.
3. h∘ψ and J∘ψ = J(f∘ψ)/Jψ are Lⁿ⌞B-a.e.-measurable.
4. Within-B Jacobians equal Jψ and J(f∘ψ) a.e. on B, by uniqueness of within-derivatives on Borel sets.
5. Injective weighted area formula for ψ on B: ∫_S h·J dHⁿ = ∫_B Jψ·(h·J)∘ψ dLⁿ.
6. Jacobian identity: Jψ·(J∘ψ) = J(f∘ψ) a.e. on B.
7. Weighted area formula, and measurability of the fibre sums, for f∘ψ on B.
8. Reindex the fibres of f∘ψ in B as the fibres of f in S via ψ.

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
