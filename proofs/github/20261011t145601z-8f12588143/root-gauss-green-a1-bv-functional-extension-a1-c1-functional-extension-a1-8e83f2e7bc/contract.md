<!-- theorem-id: gmt-ch03/root.gauss_green-a1.bv_functional_extension-a1.c1_functional_extension-a1 -->

## Theorem `Submission.gaussGreenRep_extend_C1_functional`

Let N ∈ ℕ, U ⊆ ℝ^N open, and Λ₀ : (ℝ^N → ℝ^N) → ℝ. Call g admissible if g is continuous with compact support and tsupport g ⊆ U, and C¹-admissible if g is C¹ with compact support and tsupport g ⊆ U. Assume:
(H_app) for every continuous g : ℝ^N → ℝ^N with compact support and every open W ⊇ tsupport g, there are a compact K with tsupport g ⊆ K ⊆ W and C¹ maps h_k : ℝ^N → ℝ^N (k ∈ ℕ), each with compact support and tsupport h_k ⊆ K, such that h_k → g uniformly on ℝ^N;
(H_add) Λ₀(g + h) = Λ₀(g) + Λ₀(h) for all C¹-admissible g, h;
(H_hom) Λ₀(c g) = c Λ₀(g) for all c ∈ ℝ and C¹-admissible g;
(H_bd) for every compact K ⊆ U there is C ≥ 0 such that |Λ₀(g)| ≤ C·M for every C¹ g with compact support and tsupport g ⊆ K and every M ∈ ℝ with |g(x)| ≤ M for all x.
Then there is Λ : (ℝ^N → ℝ^N) → ℝ such that:
(a) Λ(g + h) = Λ(g) + Λ(h) for all admissible g, h;
(b) Λ(c g) = c Λ(g) for all c ∈ ℝ and admissible g;
(c) for every compact K ⊆ U there is C ∈ ℝ with Λ(g) ≤ C for every continuous g with tsupport g ⊆ K and |g(x)| ≤ 1 for all x;
(d) Λ(g) = Λ₀(g) for every C¹-admissible g.

Node: `root.gauss_green-a1.bv_functional_extension-a1.c1_functional_extension-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/122

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.gaussGreenRep_extend_C1_functional`

```lean
∀ (N : ℕ) (U : Set (Rn N)) (Λ₀ : (Rn N → Rn N) → ℝ), IsOpen U → (∀ (g : Rn N → Rn N) (W : Set (Rn N)), Continuous g → HasCompactSupport g → IsOpen W → tsupport g ⊆ W → ∃ K : Set (Rn N), IsCompact K ∧ tsupport g ⊆ K ∧ K ⊆ W ∧ ∃ h : ℕ → Rn N → Rn N, (∀ k, ContDiff ℝ 1 (h k) ∧ HasCompactSupport (h k) ∧ tsupport (h k) ⊆ K) ∧ TendstoUniformly h g atTop) → (∀ g h : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ U → ContDiff ℝ 1 h → HasCompactSupport h → tsupport h ⊆ U → Λ₀ (g + h) = Λ₀ g + Λ₀ h) → (∀ (c : ℝ) (g : Rn N → Rn N), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ U → Λ₀ (c • g) = c * Λ₀ g) → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, (∀ x, ‖g x‖ ≤ M) → |Λ₀ g| ≤ C * M) → ∃ Λ : (Rn N → Rn N) → ℝ, (∀ g h : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Continuous h → HasCompactSupport h → tsupport h ⊆ U → Λ (g + h) = Λ g + Λ h) ∧ (∀ (c : ℝ) (g : Rn N → Rn N), Continuous g → HasCompactSupport g → tsupport g ⊆ U → Λ (c • g) = c * Λ g) ∧ (∀ K : Set (Rn N), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ g : Rn N → Rn N, Continuous g → tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → Λ g ≤ C) ∧ ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ U → Λ g = Λ₀ g
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

- Parent DAG node: `root.gauss_green-a1.bv_functional_extension-a1`
- Child DAG node: `root.gauss_green-a1.bv_functional_extension-a1.c1_functional_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 4-10 of the parent proof. The underlying text is the remark after Simon Ch. 2, (2.1) (chapter-02.txt lines 480-498, printed p. 48): "the functional ∫_U u div g extends uniquely to give a (real-valued) linear functional on K(U, ℝ^n) ... which is bounded on K_W(U, ℝ^n) for every W ⊂⊂ U". Here the BV functional is replaced by an arbitrary Λ₀ satisfying (H_add), (H_hom) and (H_bd). The uniform C¹ approximation theorem is taken as hypothesis (H_app); its exact statement is that of the parent's sibling gaussGreenRep_c1_uniform_approx, which the parent uses to discharge it. SimonGMT Chapter08/FirstVariationExtension.lean builds the same extension for varifold first variation via LinearMap.extendOfNorm on fixed-support spaces. The sequential argument below avoids building normed spaces.

Terminology. A field g is admissible if g is continuous, has compact support and tsupport g ⊆ U. It is C¹-admissible if g is C¹, has compact support and tsupport g ⊆ U. For admissible g, a sequence (h_k)_{k∈ℕ} is an approximating sequence for g if there is a compact L ⊆ U such that:
- every h_k is C¹ with compact support and tsupport h_k ⊆ L;
- h_k → g uniformly on ℝ^N, i.e. for every δ > 0 there is k₀ with |h_k(x) − g(x)| < δ for all k ≥ k₀ and all x.
For a compact L ⊆ U, C(L) ≥ 0 denotes a constant given by (H_bd).

1. Differences. If g, h are C¹-admissible, then Λ₀(g − h) = Λ₀(g) − Λ₀(h). Indeed, −h is C¹ with compact support and tsupport(−h) = tsupport h ⊆ U. Since (−1)·h = −h, (H_hom) gives Λ₀(−h) = −Λ₀(h). As g − h = g + (−h), (H_add) gives Λ₀(g − h) = Λ₀(g) + Λ₀(−h) = Λ₀(g) − Λ₀(h).

2. Lipschitz estimate. Let L ⊆ U be compact and C = C(L). Let g, h be C¹ with compact support and tsupports in L, and suppose |g(x) − h(x)| ≤ M for all x. Then |Λ₀(g) − Λ₀(h)| ≤ C·M. Indeed, g − h is C¹ with compact support, and tsupport(g − h) ⊆ tsupport g ∪ tsupport(−h) = tsupport g ∪ tsupport h ⊆ L. So (H_bd) gives |Λ₀(g − h)| ≤ C·M. Moreover Λ₀(g − h) = Λ₀(g) − Λ₀(h) by step 1, since g and h are C¹-admissible (L ⊆ U).

3. An inequality. For C ≥ 0 and ε > 0, put δ := ε/(2(C + 1)) > 0. Then C·(2δ) = ε·C/(C + 1) < ε, since 0 ≤ C/(C + 1) < 1. In particular C·δ ≤ C·(2δ) < ε.

4. Cauchy property. Let (h_k) be an approximating sequence for an admissible g, with compact set L, and let C = C(L). Given ε > 0, let δ be as in step 3, and choose k₀ such that |h_k(x) − g(x)| < δ for all k ≥ k₀ and all x. For k ≥ k₀ and all x, |h_k(x) − h_{k₀}(x)| ≤ |h_k(x) − g(x)| + |h_{k₀}(x) − g(x)| ≤ 2δ. By step 2, |Λ₀(h_k) − Λ₀(h_{k₀})| ≤ C·2δ < ε. So (Λ₀(h_k))_k is a Cauchy sequence of reals (Metric.cauchySeq_iff'), and it converges because ℝ is complete (cauchySeq_tendsto_of_complete).

5. Independence. Let (h_k) and (h'_k) be approximating sequences for the same admissible g, with compact sets L and L', and suppose Λ₀(h_k) → ℓ and Λ₀(h'_k) → ℓ'. The set L ∪ L' ⊆ U is compact; let C = C(L ∪ L'). Given ε > 0 and δ as in step 3, for all sufficiently large k we have |h_k(x) − g(x)| < δ and |h'_k(x) − g(x)| < δ for all x, hence |h_k(x) − h'_k(x)| ≤ 2δ. All supports lie in L ∪ L', so step 2 gives |Λ₀(h_k) − Λ₀(h'_k)| ≤ C·2δ < ε. Hence Λ₀(h_k) − Λ₀(h'_k) → 0. This sequence also tends to ℓ − ℓ', so ℓ = ℓ' by uniqueness of limits in ℝ.

6. Existence of approximating sequences. Let g be admissible. Applying (H_app) with W := U (open, with tsupport g ⊆ U) yields a compact K ⊆ U and C¹ fields h_k with compact support, tsupport h_k ⊆ K and h_k → g uniformly. This is an approximating sequence for g, with L := K.

7. Definition of Λ and the key property. Using choice, fix for every admissible g an approximating sequence (s_g(k))_k from step 6. For non-admissible g put s_g(k) := 0. Define Λ(g) := lim_{k→∞} Λ₀(s_g(k)); in Lean, Λ g := limUnder atTop (fun k ↦ Λ₀ (s_g k)). For admissible g this limit exists by step 4; for non-admissible g its value is irrelevant.
Key property (★): if g is admissible and (h_k) is any approximating sequence for g, then Λ₀(h_k) → Λ(g). Proof: by step 4, Λ₀(h_k) → ℓ for some ℓ, and Λ₀(s_g(k)) → Λ(g) (CauchySeq.tendsto_limUnder). By step 5 applied to (h_k) and (s_g(k)), ℓ = Λ(g).

8. Proof of (d). Let g be C¹-admissible. Then g is admissible, since C¹ maps are continuous. The constant sequence h_k := g is an approximating sequence for g with L := tsupport g, which is compact (g has compact support) and contained in U; uniform convergence is trivial. By (★) the constant sequence Λ₀(g) converges to Λ(g), so Λ(g) = Λ₀(g).

9. Proof of (a). Let g, h be admissible, with approximating sequences (s_k) (compact L) and (s'_k) (compact L') from step 6.
- g + h is admissible: it is continuous, has compact support, and tsupport(g + h) ⊆ tsupport g ∪ tsupport h ⊆ U.
- (s_k + s'_k) is an approximating sequence for g + h. Each s_k + s'_k is C¹ with compact support, and tsupport(s_k + s'_k) ⊆ L ∪ L', a compact subset of U. Also s_k + s'_k → g + h uniformly, because |(s_k + s'_k)(x) − (g + h)(x)| ≤ |s_k(x) − g(x)| + |s'_k(x) − h(x)| (TendstoUniformly.add).
By (★), Λ₀(s_k + s'_k) → Λ(g + h). Since s_k and s'_k are C¹-admissible, (H_add) gives Λ₀(s_k + s'_k) = Λ₀(s_k) + Λ₀(s'_k), which tends to Λ(g) + Λ(h) by (★) for g and for h. By uniqueness of limits, Λ(g + h) = Λ(g) + Λ(h).

10. Proof of (b). Let c ∈ ℝ and let g be admissible with approximating sequence (s_k) (compact L).
- c g is admissible: it is continuous, and support(c g) ⊆ support g, so c g has compact support and tsupport(c g) ⊆ tsupport g ⊆ U.
- (c s_k) is an approximating sequence for c g. Each c s_k is C¹ with compact support, and tsupport(c s_k) ⊆ tsupport s_k ⊆ L. Moreover |c s_k(x) − c g(x)| = |c|·|s_k(x) − g(x)|. So for ε > 0, once |s_k(x) − g(x)| < ε/(|c| + 1) for all x, we get |c s_k(x) − c g(x)| ≤ |c|·ε/(|c| + 1) < ε for all x.
By (★), Λ₀(c s_k) → Λ(c g). By (H_hom), Λ₀(c s_k) = c·Λ₀(s_k), which tends to c·Λ(g). Hence Λ(c g) = c·Λ(g).

11. Proof of (c). Let K ⊆ U be compact. Choose an open W with K ⊆ W, closure W compact and closure W ⊆ U (exists_open_between_and_isCompact_closure; ℝ^N is locally compact and regular). Let C := C(closure W) ≥ 0 from (H_bd); C depends only on K.
Let g be continuous with tsupport g ⊆ K and |g(x)| ≤ 1 for all x. Since tsupport g is a closed subset of the compact K, g has compact support (IsCompact.of_isClosed_subset); and tsupport g ⊆ U. So g is admissible.
Apply (H_app) to g and the open set W (tsupport g ⊆ K ⊆ W). This gives a compact K'' ⊆ W and C¹ fields h_k with compact support, tsupport h_k ⊆ K'' ⊆ W ⊆ closure W ⊆ U, and h_k → g uniformly. This is an approximating sequence for g (with L := K''), so Λ₀(h_k) → Λ(g) by (★).
Let ε > 0 and δ := ε/(2(C + 1)). For all large k and all x, |h_k(x) − g(x)| < δ, hence |h_k(x)| ≤ |h_k(x) − g(x)| + |g(x)| ≤ 1 + δ. Since tsupport h_k ⊆ closure W, (H_bd) gives Λ₀(h_k) ≤ |Λ₀(h_k)| ≤ C·(1 + δ). Passing to the limit (le_of_tendsto): Λ(g) ≤ C·(1 + δ) = C + C·δ < C + ε, by step 3. As ε > 0 is arbitrary, Λ(g) ≤ C (le_of_forall_pos_lt_add).

12. Steps 8-11 establish (a), (b), (c) and (d) for the function Λ of step 7. ∎

Lean remarks (checked in a scratch elaboration against GMT.Ch03.Submission):
- For constant multiples use ContDiff.const_smul c, Continuous.const_smul c and HasCompactSupport.smul_left, and get tsupport(c • g) ⊆ tsupport g from closure_mono (Function.support_const_smul_subset c g). Applying tsupport_smul_subset_right to c • g on EuclideanSpace hit the heartbeat limit.
- For Λ₀(−h) use neg_one_smul ℝ h : (−1 : ℝ) • h = −h, with tsupport_neg, HasCompactSupport.neg and ContDiff.neg.

## Key steps

1. Λ₀ respects differences, and |Λ₀ g − Λ₀ h| ≤ C(L)·sup|g − h| for C¹ fields supported in a compact L ⊆ U.
2. Along an approximating sequence (C¹ fields supported in a fixed compact L ⊆ U, converging uniformly), Λ₀ is Cauchy; two approximating sequences of the same g have the same limit.
3. (H_app) with W := U gives an approximating sequence for every admissible g. Define Λ(g) as the limit along a chosen one; then Λ₀(h_k) → Λ(g) along every approximating sequence.
4. (d) via constant sequences; (a) and (b) by adding or scaling approximating sequences and using (H_add)/(H_hom).
5. (c): approximate inside an open W ⊂⊂ U containing K. Then |h_k| ≤ 1 + δ with supports in closure W, and (H_bd) gives Λ(g) ≤ C(closure W)(1 + δ) for every δ > 0.

## Reference use

### local-project

Queries:
- `diff <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean (identical); grep -n '### 11' -A 6 <snapshot>/project/GMT/Ch03/README.md; grep -n 'def HasLocallyFinitePerimeter' -A 3 <snapshot>/project/GMT/Ch03/Contract.lean`
- `cat Poincare/SimonGMT/Chapter02/BV.lean (IsLocallyBV, IsRelativelyCompactIn, IsC1TestField, euclideanDivergence, euclideanDivergence_eq_sum_inner, support_euclideanDivergence_subset, compactlySupportedSupNorm)`
- `sed -n 25,60p Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `rg -l -i 'extend|extension|mollif|tendstoUniformly|IsLocallyBV|euclideanDivergence' Poincare/SimonGMT; grep -n '^theorem\|^def' Chapter08/FirstVariationRiesz.lean; sed -n 1,330p Chapter08/FirstVariationExtension.lean; sed -n 100,200p Chapter08/FirstVariationBounds.lean`
- `rg -n 'theorem exists_open_between_and_isCompact_closure' -A4 mathlib/Mathlib`
- `rg -n 'theorem integral_indicator₀|theorem integral_indicator ' -A3 mathlib/Mathlib`
- `rg -n 'theorem fderiv_neg\b|theorem fderiv_add\b|theorem fderiv_const_smul\b|theorem fderiv_const_smul_of_field|theorem fderiv_sub\b' -A3 mathlib/Mathlib`
- `rg -n 'theorem Continuous.integrable_of_hasCompactSupport|theorem ContDiff.continuous_fderiv\b|theorem cauchySeq_tendsto_of_complete|theorem tendstoUniformly_iff|theorem tsupport_smul_subset_right|theorem HasCompactSupport.smul_left\b|theorem tendsto_nhds_unique\b|theorem ContDiff.differentiable\b|theorem CauchySeq.tendsto_limUnder|theorem cauchySeq_iff.|theorem dist_smul₀|theorem integral_const_mul\b|theorem integral_add\b' mathlib/Mathlib`
- `rg -n 'HasCompactSupport.inv\b|tsupport_mul_subset|TendstoUniformly.mul\b|tendstoUniformly_const|theorem tsupport_smul_subset|HasCompactSupport.smul' mathlib/Mathlib/Topology/Algebra/Support.lean mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `rg -n 'const_smul' mathlib/Mathlib/Algebra/Module/Basic.lean (support_const_smul_subset)`
- `rg -n 'theorem Continuous.exists_contDiff_approx|theorem Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le' -A 8 mathlib/Mathlib; rg -n 'def extendOfNorm|theorem extendOfNorm_eq|theorem norm_extendOfNorm_apply_le' mathlib/Mathlib`
- `sed -n 474,532p book/chapter-02.txt; grep -n 'Notice that this means that\|extends uniquely' book/chapter-02.txt`
- `lake env lean /tmp/bvext_decomp/Stmts.lean and /tmp/bvext_decomp/Full.lean (import GMT.Ch03.Submission + contract namespace/opens): elaborate and fully prove the 3 child statements plus an assembly theorem (children + gaussGreenRep_c1_uniform_approx frozen type ⇒ parent frozen type); #print axioms`
- `lake env lean /tmp/bvext_decomp/SmulTest.lean: elaboration variants for c • g on Rn N`
- `python3 scan of dag.json nodes[*].lean_name and nodes[*].theorems for collisions with the proposed names; byte-identity check of assembly conclusion vs parent lean_statement and approx hypothesis vs sibling lean_statement`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/MulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Algebra/Module/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Manifold/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Operator/Extend.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-bv-functional-extension-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-c1-uniform-approx-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`

**Snapshot.** Project d09bc8a, Mathlib 25730c7c. The snapshot's Contract.lean is byte-identical to the workspace contract, and HasLocallyFinitePerimeter U E is IsLocallyBV U χ_E.

**Found and used by the children:**
- **SimonGMT Chapter02** (children 1, 2): euclideanDivergence, euclideanDivergence_eq_sum_inner, support_euclideanDivergence_subset, IsLocallyBV (with IsRelativelyCompactIn, IsC1TestField, compactlySupportedSupNorm = sSup of the range of the norm).
- **Mathlib, calculus and integration:** exists_open_between_and_isCompact_closure (Topology/Separation/Regular.lean); integral_indicator and integral_indicator₀ (Bochner/Set.lean); fderiv_add, fderiv_const_smul, fderiv_neg (FDeriv/Add.lean; fderiv_neg needs no differentiability); ContDiff.continuous_fderiv and ContDiff.differentiable (n ≠ 0 form); Continuous.integrable_of_hasCompactSupport; integral_add; integral_const_mul.
- **Mathlib, limits:** Metric.cauchySeq_iff', cauchySeq_tendsto_of_complete, CauchySeq.tendsto_limUnder, Metric.tendstoUniformly_iff, TendstoUniformly.add (to_additive of TendstoUniformly.mul), tendsto_nhds_unique, dist_smul₀.
- **Mathlib, supports:** HasCompactSupport.smul_left; Function.support_const_smul_subset (Algebra/Module/Basic.lean).

**Template found.** SimonGMT Chapter08/FirstVariationExtension.lean extends varifold first variation from C¹ to continuous fields via LinearMap.extendOfNorm (Analysis/Normed/Operator/Extend.lean). It is stated for Varifold/TestVectorField, so it is cited only as a template for child 3.

**No match:**
- SimonGMT has no extension of the IsLocallyBV functional and no linearity lemma for integrals of euclideanDivergence. Chapter03/FinitePerimeter.lean only packages a pair as data.
- Mathlib has neither result. Mathlib's Continuous.exists_contDiff_approx (support-preserving) exists, but child 3 follows the parent proof and takes the sibling's approximation theorem as hypothesis (H_app).

**Pitfall found by test elaboration.** On Rn N, tsupport_smul_subset_right applied to c • g hits the heartbeat limit, while closure_mono (Function.support_const_smul_subset c g) works. This is recorded in child 3's Lean remarks.

**Verification.**
- All three frozen child statements elaborate and were fully proved in /tmp/bvext_decomp/Full.lean against GMT.Ch03.Submission.
- The assembly (children + gaussGreenRep_c1_uniform_approx type ⇒ the parent's byte-identical frozen type) compiles.
- #print axioms gives only propext, Classical.choice and Quot.sound.
- The proposed lean_names collide with no dag.json lean_name or theorems entry (111 nodes).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
