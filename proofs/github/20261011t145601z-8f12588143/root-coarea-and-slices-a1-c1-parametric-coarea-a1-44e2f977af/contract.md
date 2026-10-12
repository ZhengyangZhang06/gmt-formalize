<!-- theorem-id: gmt-ch03/root.coarea_and_slices-a1.c1_parametric_coarea-a1 -->

## Theorem `Submission.c1_parametric_coarea_formula`

Let m, k ∈ ℕ with m > 0 and k > 0, n := m + k, N ∈ ℕ, D ⊆ ℝⁿ open, ψ : ℝⁿ → ℝ^N of class C¹ on D and injective on D, and G : ℝⁿ → ℝᵐ of class C¹. For u ∈ D let K(u) := ker DG(u), ι_{K(u)} its inclusion, and J(u) := normDet(Dψ(u) ∘ ι_{K(u)})·normDet(DG(u)*). Then for every Borel B ⊆ D and every Borel φ : ℝ^N → [0, ∞]: the function y ↦ ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ is Lᵐ-a.e. measurable, and ∫_B φ(ψ(u))·J(u) dLⁿ(u) = ∫_{ℝᵐ} ∫_{ψ(B ∩ G⁻¹{y})} φ dHᵏ dLᵐ(y). Notation (as in the parent): ℝ^d = Rn d = EuclideanSpace ℝ (Fin d); Hˢ = μHE[s] (applied to an arbitrary set it is the Hausdorff outer measure); Lᵈ = volume; normDet = Mathlib's LinearMap.normDet; P* = LinearMap.adjoint P; DF(u) = fderiv ℝ F u.

Node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/28

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/133

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/601, https://github.com/ZhengyangZhang06/gmt-formalize/issues/602, https://github.com/ZhengyangZhang06/gmt-formalize/issues/603, https://github.com/ZhengyangZhang06/gmt-formalize/issues/604, https://github.com/ZhengyangZhang06/gmt-formalize/issues/605, https://github.com/ZhengyangZhang06/gmt-formalize/issues/607

## Lean problem

Declaration: `Submission.c1_parametric_coarea_formula`

```lean
∀ (m k N : ℕ) (D : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m), 0 < m → 0 < k → IsOpen D → ContDiffOn ℝ 1 ψ D → InjOn ψ D → ContDiff ℝ 1 G → ∀ B ⊆ D, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → AEMeasurable (fun y : Rn m ↦ ∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) volume ∧ ∫⁻ u in B, φ (ψ u) * ENNReal.ofReal (((fderiv ℝ ψ u).toLinearMap ∘ₗ (LinearMap.ker (fderiv ℝ G u).toLinearMap).subtype).normDet * (LinearMap.adjoint (fderiv ℝ G u).toLinearMap).normDet) = ∫⁻ y, (∫⁻ x in ψ '' (B ∩ G ⁻¹' {y}), φ x ∂μHE[k]) ∂volume
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

- Parent DAG node: `root.coarea_and_slices-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Lemmas L2, LA and L3 (Simon Ch. 2, (6.3), (6.6), chapter-02.txt lines 1410-1510, whose proof Simon omits; standard proof [Fed69, 3.2.12, 3.2.22] / Evans-Gariepy Thm 3.11: implicit function theorem + Fubini on the regular set, the critical set by L1). Specializations stated explicitly: B and φ are Borel (all the parent's assembly needs), ψ is only assumed C¹ and injective on D (the parent's bi-Lipschitz and injective-derivative assumptions are not used here), and the integrand is written in the form J(u) = normDet(Dψ(u)∘ι_{K(u)})·normDet(DG(u)*), which equals the parent's J*(u)·Jψ(u) by the chain-rule half of the parent's LA (that conversion is not needed here; in this decomposition it is performed for the manifold M by the sibling chart_coarea_jacobian_identification); accordingly step 3 below is the 'flat' half of the parent's LA.
0. (Preliminaries.) (a) ψ is locally Lipschitz on D: each u ∈ D has a closed ball in D on which ‖Dψ‖ is bounded (Dψ is continuous on the open D), so ψ is Lipschitz there by the mean value inequality, and countably many such balls cover D. Hence Hᵏ(ψ(S)) = 0 whenever S ⊆ D and Hᵏ(S) = 0 (Hᵏ(ψ(S ∩ ball)) ≤ Lipᵏ·Hᵏ(S ∩ ball), SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn). (b) If S ⊆ D is Borel then ψ(S) is Borel (ψ is continuous and injective on the Borel subset S of the Polish space ℝⁿ: Lusin-Souslin, Mathlib MeasurableSet.image_of_continuousOn_injOn). For every y, B ∩ G⁻¹{y} is Borel, so every inner integral is the integral of a Borel function over a Borel set. (c) (Countable additivity.) If B = ⨆_t B_t is a countable disjoint union of Borel sets, then for each y the sets ψ(B_t ∩ G⁻¹{y}) are Borel and pairwise disjoint (ψ injective on D), so ∫_{ψ(B∩G⁻¹{y})} φ dHᵏ = Σ_t ∫_{ψ(B_t∩G⁻¹{y})} φ dHᵏ (lintegral_iUnion). Hence if both claims hold for every B_t, they hold for B: the left side is countably additive in B, a countable sum of a.e.-measurable functions is a.e.-measurable (AEMeasurable.ennreal_tsum), and ∫ Σ_t = Σ_t ∫ (lintegral_tsum).
1. (Critical part.) Let C := {u ∈ D : DG(u) is not surjective}. If B ⊆ C then for u ∈ B, DG(u)* is not injective, so normDet(DG(u)*) = 0, J(u) = 0 and the left side is 0. By the sibling c1_critical_slices_null (k > 0, G C¹), Hᵏ({DG not surjective} ∩ G⁻¹{y}) = 0 for Lᵐ-a.e. y; for such y, Hᵏ(B ∩ G⁻¹{y}) = 0, so by 0(a) Hᵏ(ψ(B ∩ G⁻¹{y})) = 0 and the inner integral is 0. Thus the inner function vanishes a.e. (so it is a.e.-measurable) and both sides are 0.
2. (Implicit-function charts; parent L2.) Let P := WithLp 2 (ℝᵐ × ℝᵏ), the product with the Euclidean norm; its Lebesgue measure corresponds to the product measure Lᵐ ⊗ Lᵏ under the measure-preserving map toLp (Mathlib WithLp.volume_preserving_toLp), which is how Tonelli is applied below, and a linear isometry e : P → ℝⁿ exists (dimensions agree; e.g. via finSumFinEquiv) and maps the Lebesgue measure of P to Lⁿ (linear isometries preserve volume). Fix u₀ ∈ D \ C, K₀ := ker DG(u₀) (dimension k) and a linear π : ℝⁿ → ℝᵏ restricting to an isomorphism K₀ → ℝᵏ (e.g. π := ι ∘ p_{K₀}, ι : K₀ → ℝᵏ a linear isometry). Φ := (G, π) : ℝⁿ → P is C¹ and DΦ(u₀) = (DG(u₀), π) is injective (DG(u₀)v = 0 and πv = 0 force v ∈ K₀ and v = 0), hence invertible. By the inverse function theorem (Mathlib ContDiffAt.toOpenPartialHomeomorph and OpenPartialHomeomorph.contDiffAt_symm; the implicit-function packaging HasStrictFDerivAt.implicitToOpenPartialHomeomorph in Mathlib/Analysis/Calculus/Implicit.lean may be used instead) there is an open O' with u₀ ∈ O' ⊆ D \ C such that Φ|_{O'} is a C¹ diffeomorphism onto an open Ω ⊆ P and DΦ(u) is invertible for u ∈ O'. For y ∈ ℝᵐ let Ω_y := {z ∈ ℝᵏ : (y, z) ∈ Ω} (open) and χ_y(z) := ψ(Φ⁻¹(y, z)) for z ∈ Ω_y. Then O' ∩ G⁻¹{y} = {Φ⁻¹(y, z) : z ∈ Ω_y}, χ_y is C¹ and injective on Ω_y, and Dχ_y(z) = Dψ(u) ∘ E_u with u := Φ⁻¹(y, z), E_u := DΦ(u)⁻¹ ∘ j, j(z) := (0, z). E_u maps ℝᵏ isomorphically onto K(u): DG(u)E_u = 0 and πE_u = id.
3. (Flat linear algebra; parent LA.) For u ∈ O': normDet(Dψ(u) ∘ E_u)·|det DΦ(u)| = J(u), where |det DΦ(u)| is the absolute determinant of e ∘ DΦ(u) : ℝⁿ → ℝⁿ (= |det| of DΦ(u) in orthonormal bases). Proof: put A := Dψ(u), Γ := DG(u) (surjective), K := K(u). (i) By Mathlib normDet_comp, normDet(A ∘ E_u) = normDet(A.domRestrict K)·normDet(E_u) (range E_u = K) and normDet(A ∘ ι_K) = normDet(A.domRestrict K)·normDet(ι_K) = normDet(A.domRestrict K). (ii) In orthonormal bases adapted to K^⊥ ⊕ K and to ℝᵐ ⊕ ℝᵏ, (Γ, π) is block lower triangular ((Γ, π)|_K = (0, π|_K)), so |det DΦ(u)| = |det(Γ|_{K^⊥})|·|det(π|_K)|. (iii) |det(Γ|_{K^⊥})| = normDet(Γ*) (Γ* maps ℝᵐ isomorphically onto K^⊥ and its matrix is the transpose of that of Γ|_{K^⊥}). (iv) E_u = (π|_K)⁻¹ as a map ℝᵏ → K, so normDet(E_u)·|det(π|_K)| = 1. Multiplying (i)-(iv) gives the claim. (The identity holds for every linear A; no injectivity of Dψ is needed.)
4. (Regular part.) Let B ⊆ O' be Borel and B' := Φ(B) ⊆ Ω (Borel: Φ|_{O'} is a homeomorphism onto the open Ω). For y ∈ ℝᵐ, B'_y := {z : (y, z) ∈ B'} ⊆ Ω_y is Borel and ψ(B ∩ G⁻¹{y}) = χ_y(B'_y). By the injective area formula on the k-dimensional parameter domain (Simon Ch. 2, (3.2), (4.13)), for every y: ∫_{χ_y(B'_y)} φ dHᵏ = ∫_{B'_y} φ(χ_y(z))·normDet(Dχ_y(z)) dLᵏ(z). In detail (no rank condition on Dχ_y is available, so the Lipschitz version is used): cover the open Ω_y by countably many open balls b_q whose closures lie in Ω_y and disjointify, S_q := (B'_y ∩ b_q) \ ⋃_{q'<q} b_{q'} (Borel, pairwise disjoint, union B'_y). On closure(b_q), χ_y is Lipschitz (C¹, mean value inequality). SimonGMT weighted_area_formula_lipschitzOn_fiberSum with s := S_q and the Borel weight φ∘χ_y gives ∫ weightedAreaFiberSum S_q χ_y (φ∘χ_y) dHᵏ = ∫_{S_q} ofReal(areaJacobianWithin χ_y S_q z)·φ(χ_y(z)) dz. Since χ_y is injective, the fibre sum equals φ·1_{χ_y(S_q)}, and χ_y(S_q) is Borel (Lusin-Souslin), so the left side is ∫_{χ_y(S_q)} φ dHᵏ. A global Lipschitz extension of χ_y|closure(b_q) agrees with χ_y on the open ball b_q, hence has derivative Dχ_y there, so by SimonGMT ae_fderivWithin_eq_of_lipschitz_extension, areaJacobianWithin χ_y S_q z = normDet(Dχ_y(z)) for a.e. z ∈ S_q. Summing over q (the images χ_y(S_q) are pairwise disjoint Borel sets by injectivity; lintegral_iUnion on both sides) gives the displayed formula. Define F : P → [0, ∞] by F(y, z) := φ(ψ(Φ⁻¹(y, z)))·normDet(Dψ(Φ⁻¹(y, z)) ∘ E_{Φ⁻¹(y, z)}) for (y, z) ∈ B' and 0 otherwise; F is Borel (φ Borel; ψ ∘ Φ⁻¹ and (y, z) ↦ Dψ(u) ∘ E_u are continuous on Ω; normDet(Q) = √det(Q*Q) is continuous in Q). By Tonelli on P = ℝᵐ × ℝᵏ (Measurable.lintegral_prod_right', lintegral_prod), y ↦ ∫ F(y, z) dz = ∫_{ψ(B∩G⁻¹{y})} φ dHᵏ is Borel, and ∫_{ℝᵐ}∫_{ψ(B∩G⁻¹{y})} φ dHᵏ dy = ∫_P F = ∫_{B'} φ(ψ(Φ⁻¹(w)))·normDet(Dψ ∘ E)(Φ⁻¹(w)) dw. By the change of variables formula for the injective C¹ map e ∘ Φ on B (Mathlib lintegral_image_eq_lintegral_abs_det_fderiv_mul, with the volume-preserving isometry e), this equals ∫_B φ(ψ(u))·normDet(Dψ(u) ∘ E_u)·|det DΦ(u)| du, which is ∫_B φ(ψ(u))·J(u) du by step 3.
5. (General Borel B ⊆ D.) D \ C is open (C is relatively closed in D: the surjective linear maps form an open set) and is covered by charts O' as in step 2; by Lindelöf, countably many O'_1, O'_2, … suffice. Put B_C := B ∩ C and B_t := (B ∩ O'_t) \ ⋃_{t'<t} O'_{t'}. These are Borel and pairwise disjoint, B = B_C ⊔ ⨆_t B_t, B_C ⊆ C and B_t ⊆ O'_t. Steps 1 and 4 give both claims for each piece, and 0(c) gives them for B. ∎

## Key steps

1. ψ is locally Lipschitz and Borel-image preserving on D; both sides are countably additive over disjoint Borel pieces.
2. Critical part: J = 0 there and its slices are Hᵏ-null for a.e. y (sibling c1_critical_slices_null), so both sides vanish.
3. Regular part: implicit-function charts Φ = (G, π) diffeomorphic onto Ω ⊆ ℝᵐ × ℝᵏ; slices are injective C¹ images χ_y(Ω_y).
4. Flat identity normDet(Dψ∘E_u)·|det DΦ(u)| = normDet(Dψ∘ι_K)·normDet(DG*).
5. Area formula on each slice, Tonelli on ℝᵐ × ℝᵏ (giving measurability in y), change of variables for Φ.
6. Lindelöf: countably many charts plus the critical set give every Borel B.

## Reference use

### local-project

Queries:
- `rg -n "^def CoareaFormula|^def SlicesAreRectifiable|^noncomputable def coareaJacobian|^noncomputable def approxTangentPlane|^def HasTangentialDifferentialAt" project/GMT/Ch03/Contract.lean`
- `rg -l -i "coarea" mathlib/Mathlib`
- `rg -l -i "\bsard\b" mathlib/Mathlib`
- `rg -n "theorem MeasurableSet.image_of_continuousOn_injOn|theorem ContinuousOn.measurableEmbedding|theorem Measurable.measurableEmbedding" mathlib/Mathlib`
- `rg -n "theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul" mathlib/Mathlib`
- `rg -n "^theorem lintegral_iUnion |^theorem lintegral_tsum|^theorem lintegral_liminf_le" mathlib/Mathlib`
- `rg -n "theorem HasLineDerivAt.unique|theorem lintegral_withDensity_eq_lintegral_mul_non_measurable|theorem isOpen_iUnion_countable" mathlib/Mathlib`
- `grep -n "theorem hausdorffMeasure_le_liminf_sum|theorem hausdorffMeasure_le_liminf_tsum" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n "def MeasureTheory.Measure.euclideanHausdorffMeasure|euclideanHausdorffMeasure_zero" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n "^theorem|^noncomputable def" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean (normDet, normDet_comp, normDet_of_subsingleton, normDet_eq_zero_iff_ker_ne_bot, normDet_sq)`
- `grep -n "toOpenPartialHomeomorph|implicitToOpenPartialHomeomorph|contDiffAt_symm" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean mathlib/Mathlib/Analysis/Calculus/Implicit.lean mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `grep -rn "ContDiffOn.exists_lipschitzOnWith|LipschitzOnWith.extend_pi|measurableSet_of_differentiableAt|measurable_fderiv|LipschitzWith.ae_differentiableAt|WithLp.volume_preserving_toLp|measurableSet_eq_fun|AEMeasurable.ennreal_tsum|Measurable.lintegral_prod_right'" mathlib/Mathlib`
- `grep -n "^theorem|^def|^noncomputable def" (SimonGMT) Chapter03/Rectifiable.lean Chapter03/SubmanifoldCover.lean Chapter02/AreaDomain.lean Chapter02/CoareaLinear.lean Chapter02/CoareaLinearAlgebra.lean Chapter02/CoareaProjection.lean`
- `grep -rn "countablyRectifiable_image_contDiffOn_open|map_withDensity_areaJacobian_eq|weighted_area_formula_volume_of_injective_derivative|euclideanHausdorffMeasure_image_le_of_lipschitzOn|exists_lipschitz_extension_finiteDimensional|ae_fderivWithin_eq_of_lipschitz_extension|HasWeightedApproximateTangentSpaceAt.unique" Poincare/SimonGMT`
- `lake env lean on the ten frozen child types in the comparator's replayed Contract scope (gmt-compare.py contract_scope + lean_contract.validate_lean_statement), and on a parent-assembly test file with the ten child types and the four sibling frozen types as stubs`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`

Snapshot project d09bc8a / Mathlib 25730c7c plus the pinned simongmt package. No match: Mathlib has no co-area formula (rg 'coarea': no file) and only a fixed-dimension Sard lemma (MeasureTheory/Function/Jacobian.lean), no C¹ Sard-type slice theorem and no countable rectifiability; SimonGMT has no nonlinear co-area formula. Hence the C¹ critical-slice estimate, the C¹ parametric co-area formula and the level-set rectifiability are supplied as children. Available and cited in the children: SimonGMT linear/projection co-area (CoareaLinear.lean, CoareaProjection.lean), Lipschitz and injective area formulas (AreaDomain.lean weighted_area_formula_lipschitzOn_fiberSum, injective_area_formula_lipschitzOn, ae_fderivWithin_eq_of_lipschitz_extension, exists_lipschitz_extension_finiteDimensional; WeightedArea.lean map_withDensity_areaJacobian_eq and weighted_area_formula_volume_of_injective_derivative for arbitrary integrands), Lipschitz image bound euclideanHausdorffMeasure_image_le_of_lipschitzOn, countablyRectifiable_image_contDiffOn_open / _iUnion / _of_measure_zero / CountablyRectifiable.mono, HasWeightedApproximateTangentSpaceAt.unique (needs only θ x ≠ 0); Mathlib normDet (normDet_comp, normDet_of_subsingleton, normDet_eq_zero_iff_ker_ne_bot, normDet_sq), μHE[d] = c_d·μH[d] with hausdorffMeasure_le_liminf_sum, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, inverse/implicit function theorem (ContDiffAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, HasStrictFDerivAt.implicitToOpenPartialHomeomorph), change of variables lintegral_image_eq_lintegral_abs_det_fderiv_mul, Lusin-Souslin MeasurableSet.image_of_continuousOn_injOn / ContinuousOn.measurableEmbedding, lintegral_iUnion (arbitrary integrand), lintegral_tsum, lintegral_liminf_le, HasLineDerivAt.unique, Rademacher LipschitzWith.ae_differentiableAt, WithLp.volume_preserving_toLp. The README marks SimonGMT Chapter03 tangentialDifferential/tangentialJacobian (Differential.lean) as unfaithful; they are not used. All ten child types elaborate in the comparator's replayed Contract scope, the sibling antecedents are byte-identical to dag.json, and the parent assembly type-checks against stubs without sorry.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
