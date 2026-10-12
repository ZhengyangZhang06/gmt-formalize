<!-- theorem-id: gmt-ch05/root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1 -->

## Theorem `Submission.rectifiableVarifold_ae_tangentProj_starProjection`

Let n >= 1 and l >= 0 be integers, U ⊆ R^{n+l} open, and V = v(M, θ) a rectifiable n-varifold in U in the sense of the contract structure RectifiableVarifold:
- M = V.carrier ⊆ U is H^n-null-measurable and countably n-rectifiable;
- θ = V.mult is positive on M and H^n⌞M-measurable;
- ∫_{M∩K} θ dH^n < ∞ for every compact K ⊆ U.
Let μ := V.weight = H^n⌞θ. Then:
(a) for μ-a.e. x, the approximate tangent space of M with respect to θ (Simon Ch. 3, Def. 1.7; SimonGMT HasWeightedApproximateTangentSpaceAt) exists, so V.tangentProj x is the orthogonal projection p_P onto some n-dimensional subspace P;
(b) the map x ↦ V.tangentProj x, with values in the continuous linear endomorphisms of R^{n+l}, is μ-a.e. strongly measurable.

Node: `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/112

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/784, https://github.com/ZhengyangZhang06/gmt-formalize/issues/788, https://github.com/ZhengyangZhang06/gmt-formalize/issues/790, https://github.com/ZhengyangZhang06/gmt-formalize/issues/792, https://github.com/ZhengyangZhang06/gmt-formalize/issues/793, https://github.com/ZhengyangZhang06/gmt-formalize/issues/794, https://github.com/ZhengyangZhang06/gmt-formalize/issues/796, https://github.com/ZhengyangZhang06/gmt-formalize/issues/799

## Lean problem

Declaration: `Submission.rectifiableVarifold_ae_tangentProj_starProjection`

```lean
∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) ∧ MeasureTheory.AEStronglyMeasurable V.tangentProj V.weight
```

### Frozen project context

`GMT/Ch05/Contract.lean` at `ea5607598f3133b40a13241f2e51517a8c6423cd` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable

/-!
# Simon, *Introduction to GMT*, Chapter 5: The Allard Regularity Theorem (pp. 103–130)

Frozen problem statement.  Conventions (Simon's "Notation", p. ix):
* `B_ρ(y)` is the **closed** ball (`Metric.closedBall`), `B̆_ρ(y)` the open ball (`Metric.ball`);
* `ℝ^{n+ℓ}` is `EuclideanSpace ℝ (Fin (n + ℓ))`, whose first `n` coordinates span `ℝⁿ × {0}`;
* `Hⁿ` is Mathlib's `μHE[n]` (normalized so that `Hⁿ = Lⁿ` on `n`-planes, as in Simon);
* `ω_n = π^{n/2}/Γ(n/2+1)`;
* `|A|` for a linear map is the inner-product (Hilbert–Schmidt) norm `(Σ_{ij} A_{ij}²)^{1/2}`
  (Simon p. ix and footnote 2 on p. 115).
* All results are stated for `n ≥ 1` (the book's `n`-dimensional setting) and arbitrary `ℓ`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace GMT.Ch05

/-- Ambient space `ℝ^{n+ℓ}`. -/
abbrev Amb (n ℓ : ℕ) := EuclideanSpace ℝ (Fin (n + ℓ))

/-- Euclidean space `ℝᵐ`. -/
abbrev Rn (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- `ω_n = π^{n/2} / Γ(n/2 + 1)` (Simon, Notation p. ix): the volume of the unit ball of `ℝⁿ`. -/
noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)

/-- Squared Hilbert–Schmidt ("inner product") norm `|A|² = Σ_i |A eᵢ|² = Σ_{i,j} A_{ji}²`
(Simon, Notation p. ix; Ch. 5 footnote 2 p. 115 and Remark 4.4). -/
noncomputable def hsNormSq {m k : ℕ} (A : Rn m →L[ℝ] Rn k) : ℝ :=
  ∑ i : Fin m, ‖A (EuclideanSpace.single i 1)‖ ^ 2

/-- Hilbert–Schmidt norm `|A| = (Σ_{i,j} A_{ji}²)^{1/2}`; for `A = Du` this is Simon's `|Du|`. -/
noncomputable def hsNorm {m k : ℕ} (A : Rn m →L[ℝ] Rn k) : ℝ :=
  Real.sqrt (hsNormSq A)

/-- The point `(x, y) ∈ ℝⁿ × ℝ^ℓ = ℝ^{n+ℓ}` (first `n` coordinates `x`, last `ℓ` coordinates `y`). -/
noncomputable def graphPoint {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ) : Amb n ℓ :=
  WithLp.toLp 2 (Fin.append (WithLp.ofLp x) (WithLp.ofLp y))

/-- `graph u = {(x, u(x)) : x ∈ D} ⊆ ℝ^{n+ℓ}` for `u : D ⊆ ℝⁿ → ℝ^ℓ`. -/
noncomputable def graphOver {n ℓ : ℕ} (u : Rn n → Rn ℓ) (D : Set (Rn n)) : Set (Amb n ℓ) :=
  (fun x => graphPoint x (u x)) '' D

/-- The coordinate plane `ℝⁿ × {0} ⊆ ℝ^{n+ℓ}`. -/
noncomputable def horizontalPlane (n ℓ : ℕ) : Submodule ℝ (Amb n ℓ) :=
  Submodule.span ℝ (Set.range fun i : Fin n => EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ))

/-- The rotated plane `q(ℝⁿ × {0})` for a linear isometry `q` of `ℝ^{n+ℓ}`. -/
noncomputable def rotatedPlane {n ℓ : ℕ} (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) : Submodule ℝ (Amb n ℓ) :=
  (horizontalPlane n ℓ).map q.toLinearEquiv.toLinearMap

/-- Simon Ch. 2 §4 (p. 55), definition preceding 4.1, with `r = 1`: `S ⊆ ℝ^N` is an
`m`-dimensional `C¹` submanifold if each `y ∈ S` has open `V ⊆ ℝᵐ`, `W ∋ y` and a 1:1 `C¹` map
`φ : V → W` with `φ(V) = W ∩ S`, `φ` proper (`K ⊆ W` compact ⇒ `φ⁻¹(K)` compact in `V`) and
`Dφ(x)` of rank `m` (injective) for all `x ∈ V`. -/
def IsC1Submanifold (m : ℕ) {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∀ y ∈ S, ∃ (V : Set (Rn m)) (W : Set (EuclideanSpace ℝ (Fin N)))
    (φ : Rn m → EuclideanSpace ℝ (Fin N)),
    IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ 1 φ V ∧ InjOn φ V ∧ φ '' V = W ∩ S ∧
    (∀ K, IsCompact K → K ⊆ W → IsCompact (V ∩ φ ⁻¹' K)) ∧
    ∀ x ∈ V, Function.Injective (fderiv ℝ φ x)

/-- `u ∈ C^{k,α}(W)` for open `W`: `u` is `C^k` on `W`, all derivatives of order `≤ k` are bounded on
`W`, and the `k`-th derivative is `α`-Hölder on `W` (finite global seminorm).  Used for the
qualitative Hölder classes of Theorem 7.1 (any fixed norm on multilinear maps gives the same class). -/
def IsHolderCkα {m k : ℕ} (j : ℕ) (α : ℝ) (u : Rn m → Rn k) (W : Set (Rn m)) : Prop :=
  ContDiffOn ℝ j u W ∧
  (∃ B : ℝ, ∀ i ≤ j, ∀ x ∈ W, ‖iteratedFDeriv ℝ i u x‖ ≤ B) ∧
  ∃ K : ℝ, ∀ x ∈ W, ∀ y ∈ W,
    ‖iteratedFDeriv ℝ j u x - iteratedFDeriv ℝ j u y‖ ≤ K * ‖x - y‖ ^ α

/-- `h` is `C^{k,α}` in the open set `U` (locally): `C^k` on `U`, and the `k`-th derivative is
`α`-Hölder on each compact subset of `U` (Simon 7.1, "a `C^{q,α}` function in `U`"). -/
def IsLocallyHolderCkα {m k : ℕ} (j : ℕ) (α : ℝ) (h : Rn m → Rn k) (U : Set (Rn m)) : Prop :=
  ContDiffOn ℝ j h U ∧
  ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
    ‖iteratedFDeriv ℝ j h x - iteratedFDeriv ℝ j h y‖ ≤ C * ‖x - y‖ ^ α

/-- A rectifiable `n`-varifold `V = v(M, θ)` in the open set `U ⊆ ℝ^{n+ℓ}`
(Simon Ch. 4, introduction p. 85, and 3.14): only the primitive data `M ⊆ U` and `θ`, with
* `M` countably `n`-rectifiable (Ch. 3, 1.1; SimonGMT `Chapter03.CountablyRectifiable`) and
  `Hⁿ`-measurable;
* `θ` positive on `M`, `Hⁿ`-measurable, and locally `Hⁿ`-integrable on `M` in `U`.
No tangent-plane data is stored: tangent planes are *defined* below (`tangentProj`) as approximate
tangent spaces where they exist (their a.e. existence is Ch. 3, 1.9, a theorem). -/
structure RectifiableVarifold (n ℓ : ℕ) (U : Set (Amb n ℓ)) where
  /-- The carrier `M`. -/
  carrier : Set (Amb n ℓ)
  /-- The multiplicity function `θ` (its values off `M` are irrelevant). -/
  mult : Amb n ℓ → ℝ
  carrier_subset : carrier ⊆ U
  nullMeasurableSet_carrier : NullMeasurableSet carrier (μHE[n] : Measure (Amb n ℓ))
  countablyRectifiable : Poincare.SimonGMT.Chapter03.CountablyRectifiable n carrier
  mult_pos : ∀ x ∈ carrier, 0 < mult x
  aemeasurable_mult : AEMeasurable mult ((μHE[n] : Measure (Amb n ℓ)).restrict carrier)
  integrableOn_mult : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U →
    IntegrableOn mult (carrier ∩ K) (μHE[n] : Measure (Amb n ℓ))

namespace RectifiableVarifold

variable {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)

/-- Simon Ch. 4, 1.1: the weight measure `μ_V = Hⁿ ⌞ θ` (with `θ = 0` off `M`). -/
noncomputable def weight : Measure (Amb n ℓ) :=
  ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).withDensity
    (fun x => ENNReal.ofReal (V.mult x))

/-- Simon Ch. 4, 1.4: `spt V = spt μ_V`, taken inside the open set `U` where `V` lives. -/
def support : Set (Amb n ℓ) := U ∩ V.weight.support

open Classical in
/-- Orthogonal projection `p_{T_x M}` onto the tangent space `T_x V` (Simon Ch. 4, 1.3): the
approximate tangent space of `M` with respect to `θ` (Ch. 3, 1.7/1.9; SimonGMT
`Chapter03.HasWeightedApproximateTangentSpaceAt`) **where it exists**, and `0` elsewhere.  It is
unique on `M` (where `θ > 0`) and exists `μ_V`-a.e. by Ch. 3, 1.9 — a theorem, not an assumption. -/
noncomputable def tangentProj (x : Amb n ℓ) : Amb n ℓ →L[ℝ] Amb n ℓ :=
  if h : ∃ P : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P
  then (Classical.choose h).starProjection else 0

/-- Tangential divergence `div_M X (x) = Σ_{i,j} e^{ij}(x) D_i X^j(x) = trace(DX(x) ∘ p_{T_x M})`
(Simon Ch. 2, 4.18; Ch. 4, 2.3). -/
noncomputable def divM (X : Amb n ℓ → Amb n ℓ) (x : Amb n ℓ) : ℝ :=
  LinearMap.trace ℝ (Amb n ℓ) ((fderiv ℝ X x).toLinearMap ∘ₗ (V.tangentProj x).toLinearMap)

/-- Simon Ch. 4, Definition 3.14: `V` has generalized mean curvature `H` in `U` if
`∫ div_M X dμ_V = -∫ X · H dμ_V` for all `X ∈ C¹_c(U; ℝ^{n+ℓ})`; the implicit requirement that the
right side exist for every such `X` is the local `μ_V`-integrability of `H` on `U`. -/
def HasGeneralizedMeanCurvature (H : Amb n ℓ → Amb n ℓ) : Prop :=
  LocallyIntegrableOn H U V.weight ∧
  ∀ X : Amb n ℓ → Amb n ℓ, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    ∫ x, V.divM X x ∂V.weight = -∫ x, inner ℝ (X x) (H x) ∂V.weight

/-- `H` is locally in `Lᵖ(μ_V)` in `U`: `∫_K |H|ᵖ dμ_V < ∞` for every compact `K ⊆ U`. -/
def LocallyLp (H : Amb n ℓ → Amb n ℓ) (p : ℝ) : Prop :=
  ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U → ∫⁻ x in K, ‖H x‖ₑ ^ p ∂V.weight < ∞

/-- `Θⁿ(μ_V, x) = t`: `μ_V(B_r(x)) / (ω_n rⁿ) → t` as `r ↓ 0` (Simon Ch. 1 §3; Ch. 4). -/
def HasDensity (x : Amb n ℓ) (t : ℝ) : Prop :=
  Tendsto (fun r : ℝ => V.weight (closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal t))

/-- Simon Ch. 5, 4.1 (p. 115): tilt-excess
`E(ξ, σ, T) = σ⁻ⁿ ∫_{B_σ(ξ)} |p_{T_x M} − p_T|² dμ_V` (Hilbert–Schmidt norm, **no** factor `1/2`;
`B_σ(ξ)` closed).  Defined by the book only when `B_σ(ξ) ⊆ U`. -/
noncomputable def tiltExcess (ξ : Amb n ℓ) (σ : ℝ) (T : Submodule ℝ (Amb n ℓ)) : ℝ :=
  (σ ^ n)⁻¹ * ∫ x in closedBall ξ σ, hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight

/-- `(σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{1/p}` as an extended real (no junk value when infinite). -/
noncomputable def scaledLpNorm (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (ξ : Amb n ℓ) (σ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (σ ^ (p - n)) * ∫⁻ x in closedBall ξ σ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)

/-- Simon Ch. 5, p. 116 (before 4.5):
`E_*(ξ, σ, T) = max{E(ξ, σ, T), δ⁻¹ (σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{2/p}}`, `δ` as in 2.3. -/
noncomputable def tiltExcessStar (H : Amb n ℓ → Amb n ℓ) (p δ : ℝ) (ξ : Amb n ℓ) (σ : ℝ)
    (T : Submodule ℝ (Amb n ℓ)) : ℝ :=
  max (V.tiltExcess ξ σ T) (δ⁻¹ * (V.scaledLpNorm H p ξ σ).toReal ^ 2)

/-- `sup {dist(x − ξ, T) : x ∈ spt V ∩ B_σ(ξ)}` (Simon 2.5), as an extended real. -/
noncomputable def heightSup (ξ : Amb n ℓ) (σ : ℝ) (T : Submodule ℝ (Amb n ℓ)) : ℝ≥0∞ :=
  ⨆ x ∈ V.support ∩ closedBall ξ σ, ENNReal.ofReal (infDist (x - ξ) (T : Set (Amb n ℓ)))

/-- The standing hypotheses 2.3 = 5.1 of Simon Ch. 5 (pp. 108, 121), for `V` with generalized
mean curvature `H` in `U`:
`θ ≥ 1 μ_V-a.e.`, `0 ∈ spt V`, `B_ρ(0) ⊆ U`, `ω_n⁻¹ ρ⁻ⁿ μ_V(B_ρ(0)) ≤ 1 + δ`,
`(ρ^{p−n} ∫_{B_ρ(0)} |H|ᵖ dμ_V)^{1/p} ≤ δ` (and `ρ > 0`). -/
def AllardHypotheses (H : Amb n ℓ → Amb n ℓ) (p δ ρ : ℝ) : Prop :=
  0 < ρ ∧ V.HasGeneralizedMeanCurvature H ∧ (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) ∧
  (0 : Amb n ℓ) ∈ V.support ∧ closedBall (0 : Amb n ℓ) ρ ⊆ U ∧
  V.weight (closedBall 0 ρ) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * ρ ^ n)) ∧
  V.scaledLpNorm H p 0 ρ ≤ ENNReal.ofReal δ

/-- Simon Ch. 5, 7.2 (p. 128): `ξ ∈ spt V` is a regular point if `B̆_ρ(ξ) ∩ spt V` is an
`n`-dimensional `C¹` submanifold of `ℝ^{n+ℓ}` for some `ρ > 0`; `reg V` is the set of regular points
(and `sing V = spt V \ reg V`). -/
def regularSet : Set (Amb n ℓ) :=
  {ξ | ξ ∈ V.support ∧ ∃ ρ > 0, IsC1Submanifold n (ball ξ ρ ∩ V.support)}

end RectifiableVarifold

open RectifiableVarifold

/-- `ρ⁻¹ sup_B |u| + sup_B |Du| + ρ^α sup_{x ≠ y ∈ B} |x − y|^{−α} |Du(x) − Du(y)|` on a set `B`
(the quantity estimated in Simon 5.2), with `Du` the derivative within `B` and `|·|` the
Hilbert–Schmidt norm; as an extended real, so suprema never take junk values. -/
noncomputable def scaledC1AlphaNorm {n ℓ : ℕ} (u : Rn n → Rn ℓ) (B : Set (Rn n)) (α ρ : ℝ) :
    ℝ≥0∞ :=
  ENNReal.ofReal ρ⁻¹ * (⨆ x ∈ B, ‖u x‖ₑ) +
  (⨆ x ∈ B, ENNReal.ofReal (hsNorm (fderivWithin ℝ u B x))) +
  ENNReal.ofReal (ρ ^ α) * ⨆ x ∈ B, ⨆ y ∈ B, ⨆ (_ : x ≠ y),
    ENNReal.ofReal (hsNorm (fderivWithin ℝ u B x - fderivWithin ℝ u B y) / ‖x - y‖ ^ α)

/-- The conclusion of Simon 5.2 for radius `γρ` and constant `C`: there are a linear isometry `q`
of `ℝ^{n+ℓ}` and `u ∈ C^{1,1−n/p}(B_{γρ}(0); ℝ^ℓ)` (closed ball) with `u(0) = 0`, `Du(0) = 0`,
`spt V ∩ B_{γρ}(0) = q(graph u) ∩ B_{γρ}(0)`, and
`ρ⁻¹ sup|u| + sup|Du| + ρ^{1−n/p} [Du]_{1−n/p} ≤ C δ^{1/(2n+2)}`. -/
def AllardConclusion {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
    (p δ ρ γ C : ℝ) : Prop :=
  ∃ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ),
    ContDiffOn ℝ 1 u (closedBall 0 (γ * ρ)) ∧ u 0 = 0 ∧
    fderivWithin ℝ u (closedBall 0 (γ * ρ)) 0 = 0 ∧
    V.support ∩ closedBall 0 (γ * ρ) =
      q '' graphOver u (closedBall 0 (γ * ρ)) ∩ closedBall 0 (γ * ρ) ∧
    scaledC1AlphaNorm u (closedBall 0 (γ * ρ)) (1 - n / p) ρ ≤
      ENNReal.ofReal (C * δ ^ (1 / (2 * (n : ℝ) + 2)))

/-- `W^{1,2}(Ω)` with weak gradient `g` (Simon, Notation p. ix): `f, g ∈ L²(Ω)` and
`∫_Ω f ∇ζ = −∫_Ω ζ g` for every `ζ ∈ C^∞_c(Ω)`. -/
def IsW12WithGradient {n : ℕ} (f : Rn n → ℝ) (g : Rn n → Rn n) (Ω : Set (Rn n)) : Prop :=
  MemLp f 2 (volume.restrict Ω) ∧ MemLp g 2 (volume.restrict Ω) ∧
  ∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
    ∫ x in Ω, f x • gradient ζ x = -∫ x in Ω, ζ x • g x

/-! ## Headline results -/

/-- **Simon Ch. 5, Lemma 2.1 (p. 107).**  Let `V = v(M, θ)` have generalized mean curvature `H` in
the open set `U ⊆ ℝ^{n+ℓ}` (no lower bound on `θ` is needed).  If `B_ρ(ξ) ⊆ U`, then for every
`n`-dimensional subspace `T`,
`E(ξ, ρ/2, T) ≤ C ρ⁻ⁿ ∫_{B_ρ(ξ)} (dist(x − ξ, T)/ρ)² dμ_V + C ρ^{2−n} ∫_{B_ρ(ξ)} |H|² dμ_V`,
with `C = C(n)` (independent of `ℓ`).  The `|H|²` term is an extended-real integral (it may be
infinite, in which case the inequality is trivial). -/
def TiltExcessHeightEstimate : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, ∀ (ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H →
  ∀ (ξ : Amb n ℓ) (ρ : ℝ), 0 < ρ → closedBall ξ ρ ⊆ U →
  ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n →
    ENNReal.ofReal (V.tiltExcess ξ (ρ / 2) T) ≤
      ENNReal.ofReal (C * (ρ ^ n)⁻¹ *
        ∫ x in closedBall ξ ρ, (infDist (x - ξ) (T : Set (Amb n ℓ)) / ρ) ^ 2 ∂V.weight) +
      ENNReal.ofReal (C * ρ ^ ((2 : ℝ) - n)) * ∫⁻ x in closedBall ξ ρ, ‖H x‖ₑ ^ 2 ∂V.weight

/-- **Simon Ch. 5, Lemma 2.5 (Affine Approximation Lemma, p. 108)**, `p > n` (standing assumption of
the chapter).  There is `C = C(n, ℓ, p) > 0` such that if `δ ∈ (0, 1/4]` and 2.3 holds, then for each
`ξ ∈ spt V ∩ B_{δρ}(0)` and `σ ∈ (0, 2δρ]` there is an `n`-dimensional subspace `T` with
`C⁻¹ (σ⁻ⁿ ∫_{B_{σ/2}(ξ)} |p_{T_x M} − p_T|² dμ_V)^{1/2}
   ≤ σ⁻¹ sup{dist(x, ξ + T) : x ∈ spt V ∩ B_σ(ξ)} + (σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{1/p}`
and `σ⁻¹ sup{dist(x, ξ + T) : x ∈ spt V ∩ B_σ(ξ)} ≤ C δ^{1/(2n+2)}`.

*Correction:* the printed first inequality of (‡) omits the mean-curvature term
`(σ^{p−n}∫|H|ᵖ)^{1/p}`; the book derives it "directly from Remark 2.2", which contains exactly this
term, so we state the inequality that the cited argument proves.  (Since this term is `≤ δ`, it
still gives the tilt bound `σ⁻ⁿ∫_{B_{σ/2}(ξ)}|p_{T_xM} − p_T|² ≤ C δ^{1/(n+1)}` used later.) -/
def AffineApproximationLemma : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C : ℝ, 0 < C ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 4 → V.AllardHypotheses H p δ ρ →
  ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ), ∀ σ : ℝ, 0 < σ → σ ≤ 2 * δ * ρ →
  ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧
    ENNReal.ofReal (C⁻¹ * Real.sqrt ((σ ^ n)⁻¹ *
        ∫ x in closedBall ξ (σ / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight)) ≤
      ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T + V.scaledLpNorm H p ξ σ ∧
    ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T ≤ ENNReal.ofReal (C * δ ^ (1 / (2 * (n : ℝ) + 2)))

/-- **Simon Ch. 5, Lemma 2.6 (Lipschitz Approximation Lemma, p. 110)**, `p > n`.  There are
`β = β(n, ℓ, p) ∈ (0, 1/4]` and `C = C(n, ℓ, p)` such that: let `L ∈ (0, 1]`,
`δ ∈ (0, (βL)^{2n+2}]`, 2.3 hold, `σ₀ = δρ`, and let `T₀ = q(ℝⁿ × {0})` (`q` a linear isometry) be a
plane with `dist(x, T₀) ≤ K δ^{1/(2n+2)} σ₀` for `x ∈ spt V ∩ B_{2σ₀}(0)`.  Then there is
`f : Bⁿ_{σ₀/2}(0) → ℝ^ℓ` with `Lip f ≤ L`, `sup |f| ≤ K δ^{1/(2n+2)} σ₀` and
`μ_V(B_{σ₀/2}(0) ∩ (spt V \ q(graph f))) + Hⁿ(B_{σ₀/2}(0) ∩ (q(graph f) \ spt V))
   ≤ C L⁻² ∫_{B_{σ₀}(0)} |p_{T_x M} − p_{T₀}|² dμ_V`.

The book takes (w.l.o.g., after a rotation) `T₀ = T(2σ₀, 0) = ℝⁿ × {0}` from Lemma 2.5, which
satisfies the height hypothesis with `K = 2C₂.₅`; we state the rotation explicitly and allow any
such plane. The statement remains true for every `K` with `β, C` independent of `K`: if the tilt of
`T₀` on `B_{σ₀}` exceeds `c²L²` the estimate holds with `f = 0`; otherwise `T₀` is `CL`-close to
`T(2σ₀, 0)` and the book's construction applies relative to `T₀`.
*Correction:* printed `sup|f| ≤ Cδ^{1/(2n+2)}` lacks the scale factor `σ₀` (cf. 2.7 and proof (7)). -/
def LipschitzApproximationLemma : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ β C : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧
  ∀ L K : ℝ, 0 < L → L ≤ 1 → 0 ≤ K →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ (β * L) ^ (2 * n + 2) → V.AllardHypotheses H p δ ρ →
  ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ,
    (∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)),
      infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) →
  ∃ f : Rn n → Rn ℓ, LipschitzOnWith (Real.toNNReal L) f (closedBall 0 (δ * ρ / 2)) ∧
    (∀ x ∈ closedBall (0 : Rn n) (δ * ρ / 2),
      ‖f x‖ ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) ∧
    V.weight (closedBall 0 (δ * ρ / 2) ∩
        (V.support \ q '' graphOver f (closedBall 0 (δ * ρ / 2)))) +
      (μHE[n] : Measure (Amb n ℓ)) (closedBall 0 (δ * ρ / 2) ∩
        (q '' graphOver f (closedBall 0 (δ * ρ / 2)) \ V.support)) ≤
      ENNReal.ofReal (C * (L ^ 2)⁻¹ * ∫ x in closedBall 0 (δ * ρ),
        hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight)

/-- **Simon Ch. 5, Corollary 2.7 (p. 113)**, `p > n`.  With the notation and assumptions of
Lemma 2.6 (as formalized in `LipschitzApproximationLemma`), `β = β(n, ℓ, p)` can be chosen so that
`sup_{ξ ∈ spt V ∩ B_{σ₀/2}(0), σ ∈ (0, σ₀/2]} σ⁻ⁿ ∫_{B_σ(ξ)} |p_{T_x M} − p_{T₀}|² dμ_V ≤ β² L²`
implies `spt V ∩ B_{σ₀/4}(0) = q(graph f) ∩ B_{σ₀/4}(0)` for some `f : Bⁿ_{σ₀/4}(0) → ℝ^ℓ` with
`Lip f ≤ L` and `sup |f| ≤ K δ^{1/(2n+2)} σ₀` (book: `C δ^{1/(2n+2)} σ₀`). -/
def LipschitzGraphCorollary : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ β : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧
  ∀ L K : ℝ, 0 < L → L ≤ 1 → 0 ≤ K →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ (β * L) ^ (2 * n + 2) → V.AllardHypotheses H p δ ρ →
  ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ,
    (∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)),
      infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) →
    (∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ / 2), ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 →
      V.tiltExcess ξ σ (rotatedPlane q) ≤ β ^ 2 * L ^ 2) →
  ∃ f : Rn n → Rn ℓ, LipschitzOnWith (Real.toNNReal L) f (closedBall 0 (δ * ρ / 4)) ∧
    (∀ x ∈ closedBall (0 : Rn n) (δ * ρ / 4),
      ‖f x‖ ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) ∧
    V.support ∩ closedBall 0 (δ * ρ / 4) =
      q '' graphOver f (closedBall 0 (δ * ρ / 4)) ∩ closedBall 0 (δ * ρ / 4)

/-- **Simon Ch. 5, Lemma 3.1 (Harmonic approximation, p. 114).**  Given `ε > 0` there is
`δ = δ(n, ε) > 0` such that if `f ∈ W^{1,2}(B)`, `B = B̆₁(0)` the open unit ball of `ℝⁿ`, satisfies
`∫_B |∇f|² ≤ 1` and `|∫_B ∇f · ∇ζ dLⁿ| ≤ δ sup |∇ζ|` for every `ζ ∈ C^∞_c(B)`, then there is a
harmonic function `u` on `B` with `∫_B |∇u|² ≤ 1` and `∫_B (u − f)² ≤ ε`.
(`sup|∇ζ| ≤ M` is expressed by quantifying over all bounds `M`; the energy integrals of `u` and
`u − f` are extended-real integrals.) -/
def HarmonicApproximationLemma : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ (f : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient f g (ball 0 1) →
    ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 ≤ 1 →
    (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 →
      ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) →
        |∫ x in ball (0 : Rn n) 1, inner ℝ (g x) (gradient ζ x)| ≤ δ * M) →
    ∃ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ^ 2 ≤ 1 ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖u x - f x‖ₑ ^ 2 ≤ ENNReal.ofReal ε

/-- **Simon Ch. 5, Theorem 4.5 (Tilt-excess Decay Theorem, p. 116)**, `p > n`.  There are
`η, δ₀ ∈ (0, 1/4]` depending only on `n, ℓ, p` such that if 2.3 holds for some `δ ∈ (0, δ₀]`, if
`σ ∈ (0, δρ/2]`, `ξ ∈ spt μ_V ∩ B_{δρ}(0)`, and `T` is any `n`-dimensional subspace, then
`E_*(ξ, ησ, S) ≤ η^{2(1−n/p)} E_*(ξ, σ, T)` for some `n`-dimensional subspace `S`. -/
def TiltExcessDecayTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p →
  ∃ η δ₀ : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
  ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 → ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ),
  ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n →
  ∃ S : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S = n ∧
    V.tiltExcessStar H p δ ξ (η * σ) S ≤ η ^ (2 * (1 - n / p)) * V.tiltExcessStar H p δ ξ σ T

/-- **Simon Ch. 5, Theorem 5.2 (Allard Regularity Theorem, p. 121).**  If `p > n` is arbitrary,
then there are `δ₀ = δ₀(n, ℓ, p)`, `γ = γ(n, ℓ, p) ∈ (0, 1)` and `C = C(n, ℓ, p)` such that the
hypotheses 5.1 (`AllardHypotheses`) with `δ ≤ δ₀` imply the existence of a linear isometry `q` of
`ℝ^{n+ℓ}` and `u = (u¹, …, u^ℓ) ∈ C^{1,1−n/p}(Bⁿ_{γρ}(0); ℝ^ℓ)` with `Du(0) = 0`,
`spt V ∩ B_{γρ}(0) = q(graph u) ∩ B_{γρ}(0)` and
`ρ⁻¹ sup|u| + sup|Du| + ρ^{1−n/p} sup_{x ≠ y ∈ Bⁿ_{γρ}(0)} |x − y|^{−(1−n/p)} |Du(x) − Du(y)|
   ≤ C δ^{1/(2n+2)}`
(balls closed; see `AllardConclusion`, which also records `u(0) = 0`, automatic since `0 ∈ spt V`).
`δ > 0` is the book's standing convention for 2.3. -/
def AllardRegularityTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p →
  ∃ δ₀ γ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 < γ ∧ γ < 1 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
    AllardConclusion V p δ ρ γ C

/-- **Simon Ch. 5, Remark 5.3 (p. 122) — the extension of Allard's theorem announced for §6.**
For every `γ ∈ (0, 1)` there is `δ₀ = δ₀(γ, n, ℓ, p) ∈ (0, 1)` such that the hypotheses 5.1 with
`δ ≤ δ₀` imply the conclusion of Theorem 5.2 on `B_{γρ}(0)`.  The constant `C` of the estimate is
allowed to depend on `γ` as well (the remark does not specify it; this is the weaker reading). -/
def AllardRegularityAnyRadius : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ γ : ℝ, 0 < γ → γ < 1 →
  ∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
    AllardConclusion V p δ ρ γ C

/-- **Simon Ch. 5, Theorem 6.1 (Conical approximation, p. 124).**  Suppose `Λ > 0`,
`λ, θ, δ ∈ (0, 1/4)`, `ξ ∈ ∂B_{1−θ}(0)`, `V = v(M, θ_V)` has generalized mean curvature
`H ∈ L¹_loc(μ)` in an open `U ⊇ B₁(0)`, `μ = μ_V`,
`|μ(B₁(0))/ω_n − μ(B_λ(0))/(ω_n λⁿ)| + sup_{r ∈ [λ,1]} r^{1−n} ∫_{B_r(0)} |H| dμ ≤ δ`
and `μ(B₁(0)) ≤ Λ`.  Then for all `ρ ∈ (0, θ]` and `τ ∈ [2λ, 1]`
`μ(B_{(1−δ^{1/4})ρ}(ξ)) − Cδ^{1/4}|log λ| ≤ τ⁻ⁿ μ(B_{τρ}(τξ)) ≤ μ(B_{(1+δ^{1/4})ρ}(ξ)) + Cδ^{1/4}|log λ|`
with `C = C(n, ℓ, Λ)`.  (The supremum condition is written pointwise in `r`; the conclusion is in
`[0, ∞]`, where `a − c ≤ b` is written `a ≤ b + c`.) -/
def ConicalApproximationTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ Λ : ℝ, 0 < Λ → ∃ C : ℝ,
  ∀ (lam θ δ : ℝ), 0 < lam → lam < 1 / 4 → 0 < θ → θ < 1 / 4 → 0 < δ → δ < 1 / 4 →
  ∀ ξ : Amb n ℓ, ‖ξ‖ = 1 - θ →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → closedBall 0 1 ⊆ U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H →
    (∀ r ∈ Icc lam 1,
      |(V.weight (closedBall 0 1)).toReal / unitBallVolume n -
          (V.weight (closedBall 0 lam)).toReal / (unitBallVolume n * lam ^ n)| +
        r ^ (1 - (n : ℝ)) * ∫ x in closedBall (0 : Amb n ℓ) r, ‖H x‖ ∂V.weight ≤ δ) →
    V.weight (closedBall 0 1) ≤ ENNReal.ofReal Λ →
  ∀ ρ ∈ Ioc 0 θ, ∀ τ ∈ Icc (2 * lam) 1,
    V.weight (closedBall ξ ((1 - δ ^ (1 / 4 : ℝ)) * ρ)) ≤
        ENNReal.ofReal (τ ^ n)⁻¹ * V.weight (closedBall (τ • ξ) (τ * ρ)) +
          ENNReal.ofReal (C * δ ^ (1 / 4 : ℝ) * |Real.log lam|) ∧
      ENNReal.ofReal (τ ^ n)⁻¹ * V.weight (closedBall (τ • ξ) (τ * ρ)) ≤
        V.weight (closedBall ξ ((1 + δ ^ (1 / 4 : ℝ)) * ρ)) +
          ENNReal.ofReal (C * δ ^ (1 / 4 : ℝ) * |Real.log lam|)

/-- **Simon Ch. 5, Theorem 7.1, first assertion (p. 127).**  If `V = v(M, θ)` has generalized mean
curvature `H` in the open set `U ⊆ ℝ^{n+ℓ}`, `H` is locally in `Lᵖ(μ_V)` for some `p > n`,
`θ ≥ 1 μ_V`-a.e. in `U`, and `ξ ∈ U` has `Θⁿ(μ_V, ξ) = 1`, then there are `ρ > 0` and an orthogonal
`Q` of `ℝ^{n+ℓ}` such that, up to a set of `Hⁿ`-measure zero, `Q ∘ τ(M) ∩ B̆_ρ(0) = graph u`
(`τ(x) = x − ξ`), where `u : W → ℝ^ℓ`, `W ∋ 0` open in `ℝⁿ`, is `C^{1,1−n/p}(W; ℝ^ℓ)` with
`u(0) = 0`, `Du(0) = 0`.  (*Erratum:* printed target `ℝ^k` means `ℝ^ℓ`.) -/
def DensityOneRegularity : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p →
    V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) →
  ∀ ξ ∈ U, V.HasDensity ξ 1 →
  ∃ ρ > 0, ∃ (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (W : Set (Rn n)) (u : Rn n → Rn ℓ),
    IsOpen W ∧ (0 : Rn n) ∈ W ∧ IsHolderCkα 1 (1 - n / p) u W ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧
    (μHE[n] : Measure (Amb n ℓ))
      (symmDiff (Q '' ((fun x => x - ξ) '' V.carrier) ∩ ball 0 ρ) (graphOver u W)) = 0

/-- **Simon Ch. 5, Theorem 7.1, second assertion (p. 127).**  In the situation of the first
assertion, if moreover `θ` is positive integer-valued `μ_V`-a.e. in `U` and `H = h` on `spt V`
(`μ_V`-a.e.) for some `h ∈ C^{q,α}` in `U` (`q ∈ {0,1,2,…}`, `α ∈ (0,1)`), then for sufficiently
small `ρ > 0` the function `u` is `C^{q+2,α}(W)` and `Θⁿ(μ_V, x) = 1` on `B̆_ρ(ξ) ∩ spt V`.
(The hypotheses `H ∈ Lᵖ_loc`, `θ ≥ 1` of the first assertion are implied here.
*Erratum:* printed "`Θⁿ(μ_V, x) ≡ 1` on `B̆_ρ(ξ)`" must be restricted to `spt μ_V`, as in the third
assertion.  The third assertion (stationarity in a `C^{q+3}` submanifold `N`) is not included: as
printed, `N` is `(n+ℓ)`-dimensional in `ℝ^{n+ℓ}`, hence open, and it reduces to this one with
`h = 0`.) -/
def DensityOneHigherRegularity : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H h : Amb n ℓ → Amb n ℓ) (q : ℕ) (α : ℝ), 0 < α → α < 1 →
    V.HasGeneralizedMeanCurvature H →
    (∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) →
    IsLocallyHolderCkα q α h U → (∀ᵐ x ∂V.weight, H x = h x) →
  ∀ ξ ∈ U, V.HasDensity ξ 1 →
  ∃ ρ > 0, ∃ (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (W : Set (Rn n)) (u : Rn n → Rn ℓ),
    IsOpen W ∧ (0 : Rn n) ∈ W ∧ IsHolderCkα (q + 2) α u W ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧
    (μHE[n] : Measure (Amb n ℓ))
      (symmDiff (Q '' ((fun x => x - ξ) '' V.carrier) ∩ ball 0 ρ) (graphOver u W)) = 0 ∧
    ∀ x ∈ ball ξ ρ ∩ V.support, V.HasDensity x 1

/-- **Simon Ch. 5, Corollary 7.3 (p. 128).**  If `V = v(M, θ)` has generalized mean curvature `H` in
the open set `U ⊆ ℝ^{n+ℓ}`, `H` is locally in `Lᵖ(μ_V)` for some `p > n`, and `θ` is positive
integer-valued `μ_V`-a.e. in `spt V`, then `reg V` is a relatively open dense subset of `spt V`:
it is open in `spt V`, and `spt V` is the closure, taken in `U`, of `reg V` (equivalently,
`sing V` is nowhere dense in `spt V`). -/
def RegularSetOpenDense : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p →
    V.HasGeneralizedMeanCurvature H → V.LocallyLp H p →
    (∀ᵐ x ∂V.weight, x ∈ V.support → ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) →
    (∃ O : Set (Amb n ℓ), IsOpen O ∧ V.regularSet = O ∩ V.support) ∧
      V.support = closure V.regularSet ∩ U

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_height_estimate-a1`
- Child DAG node: `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 3 — Lemma 1.2 ("only if") with Remark 1.3, Theorem 1.6 ("=>") with Remarks 1.5(2),(3), Remark 1.8(1) and Theorem 1.9 (printed proofs, pp. 69-75), with details filled in.

Adaptations:
- θ is integrable only on compact subsets of the open set U; this is handled by exhausting U.
- The measurability of x ↦ p_{T_xM} is implicit in the book (Remark 1.5(2); Ch. 3 §2); it is proved here explicitly.

Correction to the printed proof of 1.6 "=>": the displayed decomposition is ∫_{η(M)} = ∫_{η(N_j)} − ∫_{η(N_j∖M_j)} + ∫_{η(M∖M_j)}. So the upper-density estimate printed with "M ∖ N_j" has to be applied to the set M ∖ M_j; step 4 below does this.

Notation.
- H^n := μHE[n] on R^{n+l} (H^n = L^n on n-planes).
- M := V.carrier, θ := V.mult, μ := V.weight = H^n⌞θ, so μ(S) = ∫_{S∩M} θ dH^n.
- η_{x,λ}(y) := λ^{-1}(y − x) = blowUpMap x λ y.
- B_r(x) is the closed ball and B°_r(x) the open ball.
- C_c is the space of compactly supported continuous f : R^{n+l} → R.
- For A ⊆ R^{n+l}, "T_xA exists (Def. 1.4)" means: there is an n-dimensional subspace P with lim_{λ↓0} ∫_{η_{x,λ}(A)} f dH^n = ∫_P f dH^n for every f ∈ C_c. Then T_xA := P.
- W(x, P) abbreviates HasWeightedApproximateTangentSpaceAt n M θ x P (Def. 1.7): finrank P = n, and for every f ∈ C_c, ∫_{η_{x,λ}(M)} f(y) θ(x + λy) dH^n(y) → θ(x) ∫_P f dH^n as λ ↓ 0.

Cited facts.
(H1) Scaling. H^n is translation invariant and H^n(λS) = λ^n H^n(S) (Mathlib Measure.euclideanHausdorffMeasure_smul₀; SimonGMT Chapter04.hausdorff_blowUp_image). Hence:
  - H^n(η_{x,λ}(S)) = λ^{-n} H^n(S);
  - ∫_{η_{x,λ}(S)} g dH^n = λ^{-n} ∫_S g∘η_{x,λ} dH^n, for H^n-measurable S and g nonnegative or integrable.
(H2) Upper Density Theorem [Ch. 1, 3.6; SimonGMT Chapter01.simon_theorem_3_6]. If ν is Borel regular and A is ν-measurable with ν(A) < ∞, then limsup_{r↓0} ν(A ∩ B_r(x))/(ω_n r^n) = 0 for H^n-a.e. x ∉ A. Consequently, for every R > 0, λ^{-n} ν(A ∩ B_{Rλ}(x)) → 0 as λ ↓ 0 at those x.
(H3) Lusin's Theorem [Ch. 1, 1.17; SimonGMT Chapter01/Lusin.lean]. Let ν be Borel regular on a metric space, A ν-measurable with ν(A) < ∞, and f : A → R ν-measurable. Then for each ε > 0 there is a closed C ⊆ A with ν(A∖C) < ε and f|_C continuous.
(H4) C^1 Approximation Theorem [Ch. 2, 1.5]. If f : R^n → R is Lipschitz and ε > 0, there is g ∈ C^1(R^n) with L^n({f ≠ g}) < ε.
(H5) Area formula [Ch. 2, 3.1-3.5]:
  - Let F be injective and Lipschitz on an open W ⊆ R^n, with values in R^{n+l}, and let h be Borel and either nonnegative or bounded with bounded support. Then ∫_{F(W)} h dH^n = ∫_W h(F(z)) JF(z) dz, where JF = det(DF^T DF)^{1/2}.
  - For injective linear L: ∫_{L(R^n)} h dH^n = JL ∫_{R^n} h(Lz) dz.
  - The image of the critical set {JF = 0} of a C^1 map is H^n-null (SimonGMT Chapter02.area_image_criticalSet_eq_zero).
  - H^n(F(Z)) <= Lip(F)^n L^n(Z) for Lipschitz F.
(H6) The inverse function theorem, in the form of Ch. 2, 4.4.

Proof.

1. Localization.
- Since U is open, choose open sets U_1 ⊆ U_2 ⊆ … with ⋃_i U_i = U and each closure(U_i) compact and contained in U. For example, U_i := {x : |x| < i, dist(x, R^{n+l}∖U) > 1/i}.
- The structure field integrableOn_mult with K = closure(U_i) gives μ(closure U_i) = ∫_{M ∩ closure U_i} θ dH^n < ∞.
- θ > 0 on M (mult_pos), so a subset of M is H^n-null iff it is μ-null. Also μ(R^{n+l}∖M) = 0.
- Hence every property that holds at H^n-a.e. point of M holds μ-a.e.

2. Lemma 1.2 ("only if"): a cover by embedded C^1 pieces.
2a. By countable rectifiability (contract field countablyRectifiable; Simon 1.1), M ⊆ M_0 ∪ ⋃_j F_j(R^n), where H^n(M_0) = 0 and each F_j : R^n → R^{n+l} is Lipschitz.
2b. Fix j. Apply (H4) to each of the n+l coordinate functions of F_j with ε = 1/(i(n+l)). This gives C^1 maps G_{ij} : R^n → R^{n+l} with L^n({F_j ≠ G_{ij}}) < 1/i. Put Z_j := R^n ∖ ⋃_i {F_j = G_{ij}}. Then:
  - L^n(Z_j) = 0;
  - F_j(R^n) ⊆ F_j(Z_j) ∪ ⋃_i G_{ij}(R^n);
  - H^n(F_j(Z_j)) = 0 by (H5).
2c. Let C_{ij} := {b : JG_{ij}(b) = 0}, a closed set. By (H5), H^n(G_{ij}(C_{ij})) = 0. On the open set O_{ij} := R^n ∖ C_{ij}, DG_{ij}(b) is injective.
2d. Fix b ∈ O_{ij}. By (H6) there are coordinate indices k_1 < … < k_n such that D(z∘G_{ij})(b) is invertible, where z : R^{n+l} → R^n is the projection onto those coordinates. Put σ := ‖D(z∘G_{ij})(b)^{-1}‖^{-1} > 0. By continuity of DG_{ij}, choose r_b > 0 such that:
  - the closed ball B_{r_b}(b) ⊆ O_{ij};
  - ‖D(z∘G_{ij})(b') − D(z∘G_{ij})(b)‖ <= σ/2 for b' ∈ B_{r_b}(b).
  The mean value inequality on this convex ball gives, for b', b'' ∈ B_{r_b}(b):
    |G_{ij}(b') − G_{ij}(b'')| >= |z(G_{ij}(b')) − z(G_{ij}(b''))| >= (σ/2)|b' − b''|.
2e. Put B := B°_{r_b}(b) and N := G_{ij}(B). Then:
  - G_{ij} is injective on B with a Lipschitz (hence continuous) inverse N → B, so G_{ij}|_B : B → N is a homeomorphism;
  - DG_{ij} is injective on B;
  - G_{ij} is Lipschitz on B with constant max_{B_{r_b}(b)} ‖DG_{ij}‖, so H^n(N) < ∞ by (H5);
  - N is σ-compact, hence Borel.
2f. By the Lindelöf property, countably many such balls cover O_{ij}. Enumerating all of them over all (i, j) gives C^1 maps G_k and open balls B_k (k >= 1), with N_k := G_k(B_k), such that:
  (i) G_k is Lipschitz on B_k; there is c_k > 0 with |G_k(b') − G_k(b'')| >= c_k |b' − b''| for b', b'' ∈ B_k; DG_k(b) is injective for b ∈ B_k; and G_k|_{B_k} : B_k → N_k is a homeomorphism;
  (ii) H^n(N_k) < ∞ and N_k is Borel;
  (iii) M ⊆ Z_0 ∪ ⋃_{k>=1} N_k, where Z_0 is a Borel H^n-null set containing M_0 ∪ ⋃_j F_j(Z_j) ∪ ⋃_{i,j} G_{ij}(C_{ij}). Such a Z_0 exists because H^n is Borel regular.
2g. Following Remark 1.3, define the pairwise disjoint Borel sets Ñ_k := N_k ∖ (Z_0 ∪ N_1 ∪ … ∪ N_{k-1}). By (iii), M ∖ Z_0 ⊆ ⋃_k Ñ_k. For x ∈ N_k put b_k(x) := (G_k|_{B_k})^{-1}(x) and P_k(x) := DG_k(b_k(x))(R^n), an n-dimensional subspace.

3. Blow-up of a C^1 piece.
Claim: for k >= 1, x ∈ N_k and f ∈ C_c, lim_{λ↓0} ∫_{η_{x,λ}(N_k)} f dH^n = ∫_{P_k(x)} f dH^n.
3a. Write G := G_k, B := B_k, b := b_k(x), L := DG(b), and choose R with spt f ⊆ B_R(0). For λ > 0 let B^λ := λ^{-1}(B − b) and Γ_λ(z) := λ^{-1}(G(b + λz) − x). Then Γ_λ is an injective map of the open set B^λ onto η_{x,λ}(N_k). It is Lipschitz and C^1, with DΓ_λ(z) = DG(b + λz).
3b. By (H5),
    ∫_{η_{x,λ}(N_k)} f dH^n = ∫_{B^λ} f(Γ_λ(z)) JG(b + λz) dz.
3c. Let z ∈ B^λ with f(Γ_λ(z)) ≠ 0. Then |G(b + λz) − G(b)| < Rλ. By 2f(i), c_k|λz| < Rλ, so |z| < R/c_k. Hence, for every λ, the integrand vanishes off B_{R/c_k}(0) and is bounded by sup|f| · sup_B JG < ∞.
3d. Fix z. B contains a ball B°_s(b), so z ∈ B^λ once λ < s/|z|. Also Γ_λ(z) → Lz and JG(b + λz) → JG(b) = JL, by differentiability of G at b and continuity of DG. So the integrand tends to f(Lz) JL.
3e. By dominated convergence, the integrals tend to JL ∫_{R^n} f(Lz) dz. By (H5) for L this equals ∫_{L(R^n)} f dH^n, and L(R^n) = P_k(x).

4. Theorem 1.6 ("=>") with Remark 1.5(2), for a set of finite measure.
4a. Let A ⊆ M be Borel with H^n(A) < ∞. Put A_0 := A ∩ Z_0 and A_k := A ∩ Ñ_k for k >= 1. These are pairwise disjoint Borel sets with A = ⋃_{k>=0} A_k, H^n(A_0) = 0 and A_k ⊆ N_k.
4b. Claim: for each k >= 1 and H^n-a.e. x ∈ A_k, T_xA exists and T_xA = P_k(x).
4c. Apply (H2) twice:
  - to ν = H^n⌞A (finite, Borel regular) with the set A ∖ A_k;
  - to ν = H^n⌞N_k (finite by 2f(ii)) with the set N_k ∖ A_k.
  Points of A_k lie in neither set. So for H^n-a.e. x ∈ A_k and every R > 0, both λ^{-n} H^n((A∖A_k) ∩ B_{Rλ}(x)) → 0 and λ^{-n} H^n((N_k∖A_k) ∩ B_{Rλ}(x)) → 0.
4d. Fix such an x and f ∈ C_c with spt f ⊆ B_R(0). Since η_{x,λ} is injective, A = A_k ⊔ (A∖A_k) and N_k = A_k ⊔ (N_k∖A_k),
    ∫_{η_{x,λ}(A)} f dH^n = ∫_{η_{x,λ}(N_k)} f dH^n − ∫_{η_{x,λ}(N_k∖A_k)} f dH^n + ∫_{η_{x,λ}(A∖A_k)} f dH^n.
  All terms are finite: f is bounded and the sets have finite H^n-measure.
4e. By (H1), for S = N_k∖A_k and for S = A∖A_k,
    |∫_{η_{x,λ}(S)} f dH^n| <= sup|f| · H^n(η_{x,λ}(S) ∩ B_R(0)) = sup|f| · λ^{-n} H^n(S ∩ B_{Rλ}(x)) → 0.
4f. With step 3, ∫_{η_{x,λ}(A)} f dH^n → ∫_{P_k(x)} f dH^n for every f ∈ C_c, that is, T_xA = P_k(x). Since H^n(A_0) = 0, T_xA exists for H^n-a.e. x ∈ A.

5. Remark 1.8(1) and Theorem 1.9: the weighted tangent space.
5a. Fix i. By aemeasurable_mult there is a Borel θ~ with θ = θ~ H^n-a.e. on M, hence μ-a.e. Let A_i := M ∩ U_i ∩ {θ = θ~}. Then A_i is μ-measurable, μ((M ∩ U_i) ∖ A_i) = 0 and μ(A_i) < ∞.
5b. Apply (H3) to the Borel regular measure μ, the set A_i and the function θ~. For each m >= 1 this gives a closed set K_{i,m} ⊆ A_i with μ(A_i ∖ K_{i,m}) < 1/m and θ|_{K_{i,m}} = θ~|_{K_{i,m}} continuous.
5c. Properties of K_{i,m}:
  - It is compact: it is closed and contained in the compact set closure(U_i).
  - It lies in M, and θ is continuous and positive on it. So θ >= c_{i,m} > 0 there, and H^n(K_{i,m}) <= μ(K_{i,m})/c_{i,m} < ∞.
  - μ((M ∩ U_i) ∖ ⋃_m K_{i,m}) = 0, so by step 1, H^n((M ∩ U_i) ∖ ⋃_m K_{i,m}) = 0.
5d. Fix K := K_{i,m}. Apply (H2) to ν = μ⌞U_i (finite, Borel regular) with the set (M ∩ U_i) ∖ K. For H^n-a.e. x ∈ K and every R > 0 this gives λ^{-n} μ(((M ∩ U_i) ∖ K) ∩ B_{Rλ}(x)) → 0. Since U_i is open and x ∈ U_i, B_{Rλ}(x) ⊆ U_i for small λ, so:
  (a) λ^{-n} μ((M∖K) ∩ B_{Rλ}(x)) → 0 for every R > 0.
  Step 4 with A = K gives:
  (b) T_xK exists for H^n-a.e. x ∈ K;
  (c) for each k >= 1, T_xK = P_k(x) for H^n-a.e. x ∈ K ∩ Ñ_k.
5e. Claim: if x ∈ K satisfies (a) and (b), then W(x, T_xK) holds.
  The dimension clause holds. Fix f ∈ C_c with spt f ⊆ B_R(0), and λ > 0 so small that B_{Rλ}(x) ⊆ U_i. The integrands below are bounded by sup|f| · θ · 1_{B_{Rλ}(x)} on M, which is μ-integrable because μ(closure U_i) < ∞. So the Bochner integrals in Def. 1.7 are genuine integrals.
  By (H1), substituting y = η_{x,λ}(z) (so θ(x + λy) = θ(z)):
    ∫_{η_{x,λ}(M)} f(y) θ(x + λy) dH^n(y) = λ^{-n} ∫_M f(η_{x,λ}(z)) θ(z) dH^n(z) = I_1 + I_2 + I_3, where
    I_1 := θ(x) λ^{-n} ∫_K f(η_{x,λ}(z)) dH^n(z) = θ(x) ∫_{η_{x,λ}(K)} f dH^n,
    I_2 := λ^{-n} ∫_K f(η_{x,λ}(z)) (θ(z) − θ(x)) dH^n(z),
    I_3 := λ^{-n} ∫_{M∖K} f(η_{x,λ}(z)) θ(z) dH^n(z).
  - By (b) and Def. 1.4, I_1 → θ(x) ∫_{T_xK} f dH^n.
  - By (a), |I_3| <= sup|f| · λ^{-n} μ((M∖K) ∩ B_{Rλ}(x)) → 0.
  - |I_2| <= sup|f| · sup_{z ∈ K ∩ B_{Rλ}(x)} |θ(z) − θ(x)| · λ^{-n} H^n(K ∩ B_{Rλ}(x)). The middle factor tends to 0 because θ|_K is continuous at x. The last factor stays bounded (Remark 1.5(3)): take g ∈ C_c with 0 <= g <= 1, g = 1 on B_R(0) and spt g ⊆ B_{2R}(0); then λ^{-n} H^n(K ∩ B_{Rλ}(x)) = H^n(η_{x,λ}(K) ∩ B_R(0)) <= ∫_{η_{x,λ}(K)} g dH^n → ∫_{T_xK} g dH^n <= ω_n (2R)^n. So I_2 → 0.
  Hence the total tends to θ(x) ∫_{T_xK} f dH^n, which proves the claim.
5f. Combining the claim with (c): for H^n-a.e. x ∈ K_{i,m} ∩ Ñ_k, W(x, P_k(x)) holds.

6. The exceptional set.
Let 𝒩 be the union of:
  - Z_0;
  - the null sets (M ∩ U_i) ∖ ⋃_m K_{i,m}, over all i;
  - for all (i, m, k), the null set of points of K_{i,m} ∩ Ñ_k at which W(x, P_k(x)) fails (step 5).
This is a countable union, so H^n(𝒩) = 0. Let x ∈ M ∖ 𝒩. Then x ∈ U_i for some i and x ∈ K_{i,m} for some m. Since x ∉ Z_0, x lies in exactly one Ñ_k (2g), and W(x, P_k(x)) holds. By step 1, μ-a.e. x lies in M ∖ 𝒩.

7. Conclusion (a).
For x ∈ M ∖ 𝒩, the condition ∃ P, HasWeightedApproximateTangentSpaceAt n M θ x P in the definition of V.tangentProj holds. So V.tangentProj x = Q_x.starProjection with Q_x := Classical.choose of that statement. The first clause of W(x, Q_x) gives finrank Q_x = n. Since μ-a.e. x lies in M ∖ 𝒩, this proves (a).

8. Conclusion (b): measurability.
8a. For x ∈ N_k let Φ_k(x) be the orthogonal projection onto P_k(x). Φ_k is continuous on N_k:
  - x ↦ b_k(x) is continuous by 2f(i);
  - b ↦ DG_k(b) is continuous;
  - for injective L, the orthogonal projection onto L(R^n) is L(L^T L)^{-1} L^T, which depends continuously on L.
8b. Define Ψ(x) := Φ_k(x) for x ∈ Ñ_k (k >= 1) and Ψ(x) := 0 for x ∉ ⋃_k Ñ_k. Ψ is Borel measurable, since the Ñ_k are disjoint Borel sets and Ψ is continuous on each.
8c. Let x ∈ M ∖ 𝒩 with x ∈ Ñ_k. Both W(x, P_k(x)) and W(x, Q_x) hold, and θ(x) > 0. By uniqueness of the weighted approximate tangent space (Simon 1.7, "evidently unique"; SimonGMT Chapter03.HasWeightedApproximateTangentSpaceAt.unique), Q_x = P_k(x). So V.tangentProj x = Φ_k(x) = Ψ(x). Hence V.tangentProj = Ψ μ-a.e.
8d. Ψ is a Borel map into the finite-dimensional, hence separable and metrizable, normed space of continuous linear endomorphisms of R^{n+l}, so it is strongly measurable. Therefore V.tangentProj is AEStronglyMeasurable with respect to μ = V.weight. This proves (b). ∎

## Key steps

1. Localize: exhaust U by relatively compact open U_i; on M, H^n-null iff mu_V-null
2. Lemma 1.2: M ⊆ Z_0 ∪ ⋃ N_k with Z_0 Borel H^n-null and N_k = G_k(B_k) embedded C^1 pieces (lower bi-Lipschitz, finite H^n), via C^1 approximation, area formula, inverse function theorem
3. Blow-ups of N_k at x converge to P_k(x) = DG_k(b_k(x))(R^n) (area formula + dominated convergence)
4. Theorem 1.6 =>: for Borel A ⊆ M of finite measure, T_xA = P_k(x) for H^n-a.e. x ∈ A ∩ Ñ_k (upper density theorem)
5. Remark 1.8(1): Lusin compacts K_{i,m} with θ continuous; W(x, T_xK) a.e. on K (upper density + continuity of θ), hence W(x, P_k(x)) a.e. on K ∩ Ñ_k
6. Outside a null set 𝒩, the 'if' in tangentProj holds: V.tangentProj x = Q_x.starProjection with finrank Q_x = n, mu_V-a.e.
7. Measurability: V.tangentProj = Ψ mu_V-a.e., where Ψ = Φ_k on Ñ_k is Borel, by uniqueness of the weighted tangent space; Ψ is strongly measurable

## Reference use

### local-project

Queries:
- `python3 -I scan of .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json nodes[*].lean_name (reserved declaration names)`
- `grep -n 'HasWeightedApproximateTangentSpaceAt\|def CountablyRectifiable\|HasApproximateTangentSpaceAt\|theorem .*ae.*tangent' -r .lake/packages/simongmt/Poincare/SimonGMT/Chapter03`
- `grep -rn 'C¹ approximation\|C1 approximation\|Approximation Theorem\|upper density\|Upper density' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01 .lake/packages/simongmt/Poincare/SimonGMT/Chapter02`
- `grep -n '^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `grep -rn 'theorem simon_theorem_1_17\|theorem area_image_criticalSet_eq_zero\|theorem hausdorff_blowUp_image\|theorem integral_weighted_blowUp\|theorem norm_normalProjection_eq_infDist' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n 'theorem (zero_of_nonpos|one_of_one_le|nonneg|le_one|contDiff|pos_of_pos)\b' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `rg -n '^theorem contDiff_infty_iff_deriv|theorem contDiffAt_norm\b|theorem trace_smulRight|starProjection_minimal|theorem infDist_eq_iInf\b|theorem starProjection_add_starProjection_orthogonal|IsProj.trace' -g '*.lean' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem hausdorffMeasure_smul|euclideanHausdorffMeasure_smul₀|hausdorffMeasure_homothety_image' -g '*.lean' <snapshot>/mathlib/Mathlib; rg -ln Lusin -g '*.lean' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem norm_fderiv_le_of_lipschitz\b\|theorem integral_hasDerivAt_right\b\|theorem contDiff_iff_contDiffAt\b\|trace_mul_comm' <snapshot>/mathlib/Mathlib/{Analysis/Calculus/FDeriv/Basic,MeasureTheory/Integral/IntervalIntegral/FundThmCalculus,Analysis/Calculus/ContDiff/Defs,LinearAlgebra/Trace}.lean`
- `diff GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean`
- `lean GMT/Ch05/Submission.lean -o /tmp/teh-decomp-elab/mybuild/GMT/Ch05/Submission.olean; lean /tmp/teh-decomp-elab/NodeCheck.lean (import GMT.Ch05.Submission + replayed contract scope + the 4 frozen child types)`
- `lean /tmp/teh-decomp-elab/Skel.lean and Skel2.lean (parent assembly from the 4 children as hypotheses; sorry-free admissibility of X)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/ClassicalTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot project/GMT/Ch05/Contract.lean is byte-identical to the workspace contract.

None of the four proposed declarations exists locally. dag.json reserves only the 13 depth-0/1 names.

Child ae_tangent_planes is a genuine open obligation:
- SimonGMT Chapter03/Rectifiable.lean defines HasWeightedApproximateTangentSpaceAt and proves .unique, but says Simon 1.6/1.9 are "not asserted here".
- SubmanifoldCover.lean has only the easy direction of Lemma 1.2.
- Differential.lean calls the existence direction of 1.6 "still-open".

Tools available for that child:
- simon_theorem_3_6 (Upper Density, Chapter01/DensityComparison.lean);
- Lusin 1.17 (Chapter01/Lusin.lean);
- area_image_criticalSet_eq_zero (Chapter02/AreaCritical.lean);
- the injective area formula (Chapter02/AreaLipschitz.lean);
- Rademacher and the Lipschitz image bound (Chapter02/Lipschitz.lean);
- Whitney C^1 extension (Chapter02/WhitneyExtension.lean), towards the missing Ch. 2, 1.5 C^1 approximation;
- Chapter04.hausdorff_blowUp_image;
- Mathlib euclideanHausdorffMeasure_smul₀ and hausdorffMeasure_homothety_image.

Child smooth_cutoff: Real.smoothTransition (contDiff, zero_of_nonpos, one_of_one_le, nonneg, le_one), contDiff_infty_iff_deriv, intervalIntegral.integral_hasDerivAt_right, contDiffAt_norm, contDiff_iff_contDiffAt, norm_fderiv_le_of_lipschitz.

Child projection_algebra: LinearMap.trace_smulRight, IsProj.trace, trace_mul_comm, Submodule.starProjection_minimal, dist_starProjection_eq_infDist, starProjection_add_starProjection_orthogonal. SimonGMT Chapter04.norm_normalProjection_eq_infDist is exactly part (ii) for a general E.

Lean checks:
- After compiling Submission.lean to an olean in /tmp, NodeCheck.lean elaborates all four frozen types in the comparator's scope (import GMT.Ch05.Submission plus the replayed open/namespace commands), with only sorry warnings.
- Skel.lean (the four children as hypotheses) elaborates the parent's infinite case, the first-variation application, the mu-a.e. divergence rewrite and the operator/distance bound.
- Skel2.lean proves sorry-free that X is C^1, compactly supported, has tsupport X ⊆ U, and that D zeta = 0 off B_rho(xi).

The book texts supply the printed proofs that are copied: Ch. 5 2.1; Ch. 3 1.2, 1.3, 1.6, 1.8, 1.9; Ch. 1 1.17, 3.6; Ch. 2 1.5, 3.1-3.5, 4.4.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
