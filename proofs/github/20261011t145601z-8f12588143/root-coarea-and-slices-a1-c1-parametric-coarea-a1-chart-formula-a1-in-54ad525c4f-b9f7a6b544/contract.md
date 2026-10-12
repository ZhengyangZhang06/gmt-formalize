<!-- theorem-id: gmt-ch03/root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1.integrand_tonelli-a1 -->

## Theorem `Submission.pcoarea_chart_integrand_tonelli`

Notation: ℝ^d = Rn d = EuclideanSpace ℝ (Fin d); n := m + k; P := WithLp 2 (ℝᵐ × ℝᵏ), the Euclidean product, whose volume is the Lebesgue measure of the finite-dimensional inner product space P (instance measureSpaceOfInnerProductSpace); toLp = WithLp.toLp 2; Hᵏ = μHE[k] (applied to an arbitrary set it is the Hausdorff outer measure); Lᵈ = volume; normDet = LinearMap.normDet, applied to the underlying linear map; DF(x) = fderiv ℝ F x (the zero map where F is not differentiable); j : ℝᵏ →L[ℝ] P is the continuous linear map z ↦ toLp(0, z), in Lean (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)) (j z = toLp(0, z) holds by rfl). For an open partial homeomorphism Φ from ℝⁿ to P: O := Φ.source and Ω := Φ.target (both open), Φ⁻¹ := Φ.symm, ρ := ψ ∘ Φ⁻¹ : P → ℝᴺ (in Lean ψ ∘ Φ.symm), h(w) := φ(ψ(Φ⁻¹ w))·ofReal(normDet(Dρ(w) ∘ j)) for w ∈ P, and F := 1_{Φ(B)}·h, i.e. F = (Φ '' B).indicator h. Statement. Let m, k, N ∈ ℕ, let Φ be an open partial homeomorphism from ℝⁿ to P, let ψ : ℝⁿ → ℝᴺ be continuous on O, let B ⊆ O be Borel and let φ : ℝᴺ → [0, ∞] be Borel. Then (i) the function y ↦ ∫_{ℝᵏ} F(toLp(y, z)) dLᵏ(z) is Borel measurable on ℝᵐ, and (ii) ∫_P F d(volume) = ∫_{ℝᵐ} ∫_{ℝᵏ} F(toLp(y, z)) dLᵏ(z) dLᵐ(y). No differentiability of ψ, Φ or Φ.symm is assumed.

Node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1.integrand_tonelli-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/605

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.pcoarea_chart_integrand_tonelli`

```lean
∀ (m k N : ℕ) (ψ : Rn (m + k) → Rn N) (Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k))), ContinuousOn ψ Φ.source → ∀ B ⊆ Φ.source, MeasurableSet B → ∀ φ : Rn N → ℝ≥0∞, Measurable φ → Measurable (fun y : Rn m ↦ ∫⁻ z : Rn k, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) (WithLp.toLp 2 (y, z))) ∧ ∫⁻ w, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) w = ∫⁻ y : Rn m, ∫⁻ z : Rn k, (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet)) (WithLp.toLp 2 (y, z))
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

- Parent DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1.integrand_tonelli-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 4 (F is Borel) and 5 (Tonelli through toLp).

1. B' := Φ(B) is Borel and B' ⊆ Ω: B ⊆ O and Φ is continuous and injective on O (Φ.continuousOn, Φ.injOn), ℝⁿ is Polish and P is a Borel space (WithLp.borelSpace), so MeasurableSet.image_of_continuousOn_injOn applies; and Φ(u) ∈ Ω for u ∈ O (Φ.map_source).

2. A Borel version of ρ. ρ = ψ ∘ Φ⁻¹ is continuous on Ω: Φ⁻¹ is continuous on Ω (Φ.continuousOn_symm) and maps Ω into O (Φ.map_target), where ψ is continuous (ContinuousOn.comp). Let ρ̃ := Ω.piecewise ρ (fun _ ↦ 0) (classical decidability). Since Ω is open, hence Borel, and the constant map is continuous on Ωᶜ, ContinuousOn.measurable_piecewise shows that ρ̃ is Borel; ρ̃ = ρ on Ω (Set.piecewise_eq_of_mem), in particular on B'.

3. The Jacobian factor is Borel. Let a(w) := ofReal(normDet(Dρ(w) ∘L j)).
- w ↦ Dρ(w) = fderiv ℝ ρ w is Borel from P to P →L[ℝ] ℝᴺ by Mathlib measurable_fderiv, which holds for every function ρ.
- L ↦ L ∘L j is continuous (Continuous.clm_comp continuous_id continuous_const).
- M ↦ normDet(M) is continuous on ℝᵏ →L[ℝ] ℝᴺ: since normDet(M) ≥ 0 (LinearMap.normDet_nonneg) and normDet(M)² = det(M† ∘L M) (ContinuousLinearMap.normDet_sq), Real.sqrt_sq gives normDet(M) = √det(M† ∘L M), and the adjoint (ContinuousLinearMap.adjoint, continuous), composition (Continuous.clm_comp), ContinuousLinearMap.continuous_det and Real.continuous_sqrt are continuous. (This is the argument of the pinned SimonGMT lemma Poincare.SimonGMT.Chapter02.continuous_normDet in Chapter02/AreaApproximation.lean; that module is not imported by GMT.Ch03.Submission, so the three-line argument is given inline.)
- ENNReal.ofReal is measurable (ENNReal.measurable_ofReal). Hence a is Borel.

4. F is Borel. 1_{B'}·h = 1_{B'}·((φ ∘ ρ̃)·a) because ρ̃ = ρ on B' (Set.indicator_congr with step 2). The right-hand side is Borel (φ, ρ̃ and a are Borel, B' is Borel: Measurable.comp, Measurable.mul, Measurable.indicator). Thus F is Borel.

5. Transport to ℝᵐ × ℝᵏ. toLp : ℝᵐ × ℝᵏ → P is measurable (WithLp.measurable_toLp) and measure preserving from volume on ℝᵐ × ℝᵏ to volume on P (WithLp.volume_preserving_toLp (Rn m) (Rn k)). Hence F ∘ toLp is Borel, and since F is measurable, MeasurePreserving.lintegral_comp gives ∫_P F = ∫_{ℝᵐ×ℝᵏ} F(toLp p) dp.

6. Tonelli. The volume of ℝᵐ × ℝᵏ is Lᵐ ⊗ Lᵏ (Measure.volume_eq_prod) and Lᵏ is σ-finite. As F ∘ toLp is measurable, lintegral_prod gives ∫_{ℝᵐ×ℝᵏ} F(toLp p) d(Lᵐ⊗Lᵏ)(p) = ∫_{ℝᵐ} ∫_{ℝᵏ} F(toLp(y, z)) dz dy; with step 5 this is (ii). Measurable.lintegral_prod_right' applied to F ∘ toLp shows that y ↦ ∫_{ℝᵏ} F(toLp(y, z)) dz is measurable, which is (i). ∎

Appendix (supplementary; the numbered argument above is complete without it). The following tactic script, placed after `theorem Submission.pcoarea_chart_integrand_tonelli : <frozen type> := by` inside `namespace GMT.Ch03` with the Contract's `open` commands and `import GMT.Ch03.Submission`, compiled in the parent's decomposition session (Lean v4.35.0-rc3, Mathlib 25730c7c) with axioms propext, Classical.choice and Quot.sound only:
```lean
  intro m k N ψ Φ hψ B hB hBm φ hφ
  classical
  set j : Rn k →L[ℝ] WithLp 2 (Rn m × Rn k) := (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)) with hj
  have hB' : MeasurableSet (Φ '' B) :=
    hBm.image_of_continuousOn_injOn (Φ.continuousOn.mono hB) (Φ.injOn.mono hB)
  have hB'Ω : Φ '' B ⊆ Φ.target := by
    rintro _ ⟨u, hu, rfl⟩; exact Φ.map_source (hB hu)
  have hρ : ContinuousOn (ψ ∘ Φ.symm) Φ.target :=
    hψ.comp Φ.continuousOn_symm (fun w hw ↦ Φ.map_target hw)
  have hρm : Measurable (Φ.target.piecewise (ψ ∘ Φ.symm) (fun _ ↦ 0)) :=
    hρ.measurable_piecewise continuousOn_const Φ.open_target.measurableSet
  have hnd : Continuous (fun M : Rn k →L[ℝ] Rn N ↦ M.toLinearMap.normDet) := by
    have heq : (fun M : Rn k →L[ℝ] Rn N ↦ M.toLinearMap.normDet) =
        fun M ↦ Real.sqrt ((M.adjoint ∘L M).det) := by
      funext M
      rw [← M.normDet_sq]
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using (Real.sqrt_sq M.normDet_nonneg).symm
    rw [heq]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  have ha : Measurable (fun w ↦ ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) :=
    ENNReal.measurable_ofReal.comp ((hnd.comp (continuous_id.clm_comp continuous_const)).measurable.comp
      (measurable_fderiv ℝ _))
  have hFeq : (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) =
      (Φ '' B).indicator (fun w ↦ φ (Φ.target.piecewise (ψ ∘ Φ.symm) (fun _ ↦ 0) w) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) := by
    apply Set.indicator_congr
    intro w hw
    simp only [Set.piecewise_eq_of_mem _ _ _ (hB'Ω hw), Function.comp_apply]
  have hFm : Measurable ((Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet))) := by
    rw [hFeq]
    exact ((hφ.comp hρm).mul ha).indicator hB'
  have hmp := WithLp.volume_preserving_toLp (Rn m) (Rn k)
  have hFp := hFm.comp (WithLp.measurable_toLp 2 (Rn m × Rn k))
  refine ⟨hFp.lintegral_prod_right', ?_⟩
  rw [← hmp.lintegral_comp hFm, Measure.volume_eq_prod]
  exact lintegral_prod _ hFp.aemeasurable
```

## Key steps

1. Φ(B) is Borel by Lusin–Souslin, and Φ(B) ⊆ Ω.
2. ρ = ψ ∘ Φ⁻¹ is continuous on the open Ω, so Ω.piecewise ρ 0 is Borel and equals ρ on Φ(B).
3. w ↦ ofReal(normDet(Dρ(w) ∘ j)) is Borel: measurable_fderiv, continuity of L ↦ L ∘ j and of normDet = √det(M†M).
4. Hence F = 1_{Φ(B)}·(φ∘ρ̃)·ofReal(normDet(Dρ ∘ j)) is Borel.
5. WithLp.volume_preserving_toLp, Measure.volume_eq_prod and lintegral_prod give ∫_P F = ∫∫ F(toLp(y, z)) dz dy; Measurable.lintegral_prod_right' gives measurability in y.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json  (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum of the snapshot copies vs the compiler-package copies (/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c) of NormDet.lean, ProdLp.lean, Lp/MeasurableSpace.lean, Function/Jacobian.lean, Haar/InnerProductSpace.lean, FDeriv/Measurable.lean and of project/GMT/Ch03/Contract.lean vs the workspace Contract (all identical; the package tree is the same Mathlib revision 25730c7c, so the remaining Mathlib files were read there)`
- `grep -n 'theorem\|lemma\|def ' Mathlib/Analysis/InnerProductSpace/NormDet.lean (normDet, normDet_nonneg, ContinuousLinearMap.normDet_sq, normDet_comp_of_finrank_eq, normDet_eq_abs_det, LinearIsometry.normDet_eq_one)`
- `grep -n 'fst|snd|fstL|sndL|inr|linearEquiv|prodContinuousLinearEquiv' Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `sed -n 1,60p Mathlib/Analysis/Normed/Lp/MeasurableSpace.lean (WithLp.measurableSpace, WithLp.borelSpace)`
- `sed -n 150,215p Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean (LinearIsometryEquiv.measurePreserving, WithLp.volume_preserving_toLp)`
- `rg -n 'theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul' -A 8 Mathlib/MeasureTheory/Function/Jacobian.lean`
- `grep -n 'variable|MeasurableSpace|OpensMeasurable' Mathlib/Analysis/Calculus/FDeriv/Measurable.lean (measurable_fderiv context)`
- `per-file grep over Mathlib/Analysis/Calculus, Mathlib/MeasureTheory, Mathlib/Geometry/Manifold/IsManifold: of_local_left_inverse|hasFDerivAt_symm|contDiffAt_symm|lintegral_prod|lintegral_prod_right'|ContinuousOn.measurable_piecewise|lintegral_indicator|setLIntegral_comp_emb|lintegral_comp_emb|EventuallyEq.fderiv_eq|ContDiffOn.differentiableOn|volume_eq_prod|setLIntegral_congr_fun`
- `grep 'continuous_normDet|Measurable.*normDet' Poincare/SimonGMT/Chapter02/*.lean Chapter03/*.lean (found Chapter02/AreaApproximation.lean continuous_normDet; not imported by GMT.Ch03.Submission)`
- `grep -rn 'pcoarea_chart|chart_slice_lintegral|integrand_tonelli|chart_change_of_variables|pointwise_jacobian' snapshot project/ and SimonGMT (no match)`
- `python3 -I scan of dag.json lean_name/theorems of all 200 nodes against the four proposed names (no collision)`
- `python3 -I gen_lean.py: gmt-compare.py contract_scope + lean_contract.validate_lean_statement, then lean ChartFormulaSplitScope.lean (exit 0)`
- `lean ChartFormulaSplitAssembly.lean (#print axioms Submission.pcoarea_formula_on_chart: propext, sorryAx, Classical.choice, Quot.sound)`
- `lean ChartFormulaSplitFull.lean (four real child proofs: propext, Classical.choice, Quot.sound; parent: plus sorryAx from the two sibling stubs)`
- `lean Inst.lean (#synth MeasureSpace/BorelSpace on WithLp 2 (Rn m × Rn k); j z = WithLp.toLp 2 (0, z) by rfl)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Lp/MeasurableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Function/Piecewise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/lakefile.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1-chart-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ChartFormulaSplitScope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ChartFormulaSplitAssembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ChartFormulaSplitFull.lean`

The snapshot is at project d09bc8a and Mathlib 25730c7c. Its Mathlib sources and Contract.lean are byte-identical to the compiler packages and the workspace. No-match results: the snapshot project and SimonGMT contain no slice, Tonelli-on-WithLp, change-of-variables-into-WithLp or chart-Jacobian lemma for this setting. None of the four proposed names exists anywhere or collides with the 200 DAG nodes. So the four children are new obligations. Every library fact the child proofs cite exists with the stated form in this snapshot. This covers the normDet API (normDet_nonneg, ContinuousLinearMap.normDet_sq, normDet_comp_of_finrank_eq, normDet_eq_abs_det, LinearIsometry.normDet_eq_one), WithLp.prodContinuousLinearEquiv, fstL, borelSpace, volume_preserving_toLp, LinearIsometryEquiv.measurePreserving, lintegral_image_eq_lintegral_abs_det_fderiv_mul (arbitrary integrand), measurable_fderiv (no hypothesis on the function), MeasurableSet.image_of_continuousOn_injOn, ContinuousOn.measurable_piecewise, lintegral_prod, Measurable.lintegral_prod_right', Measure.volume_eq_prod, lintegral_indicator, setLIntegral_congr_fun, MeasurePreserving.setLIntegral_comp_emb, Filter.EventuallyEq.fderiv_eq, HasFDerivAt.unique and congr_of_eventuallyEq, and ContDiffOn.differentiableOn (n ≠ 0). SimonGMT's continuous_normDet (Chapter02/AreaApproximation.lean) is not imported by GMT.Ch03.Submission, so its three-line argument is reproduced inline. Lean results: all four types elaborate in the comparator's Contract scope; the parent assembly proves the exact frozen type from them; and each child was itself proved in full with only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
