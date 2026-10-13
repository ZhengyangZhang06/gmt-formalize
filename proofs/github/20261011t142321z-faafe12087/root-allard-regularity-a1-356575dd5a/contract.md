<!-- theorem-id: gmt-ch05/root.allard_regularity-a1 -->

## Theorem `Submission.allard_regularity_theorem`

For n >= 1, l, p > n there are delta_0, gamma in (0,1) and C, depending only on n,l,p, such that for every open U, V with generalized mean curvature H, 0 < delta <= delta_0 and rho with AllardHypotheses H p delta rho, AllardConclusion V p delta rho gamma C holds: there are a linear isometry q of R^(n+l) and u: R^n -> R^l, C^1 on the closed ball B^n_{gamma rho}(0), with u(0) = 0, Du(0) = 0 (derivative within the ball), spt V cap B_{gamma rho}(0) = q(graph u over B^n_{gamma rho}(0)) cap B_{gamma rho}(0), and rho^-1 sup|u| + sup|Du| + rho^(1-n/p) sup_{x != y} |x - y|^-(1-n/p) |Du(x) - Du(y)| <= C delta^(1/(2n+2)) (suprema over the closed ball, Hilbert-Schmidt norms, in [0,inf]).

Node: `root.allard_regularity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/113, https://github.com/ZhengyangZhang06/gmt-formalize/issues/115, https://github.com/ZhengyangZhang06/gmt-formalize/issues/118

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/578, https://github.com/ZhengyangZhang06/gmt-formalize/issues/580, https://github.com/ZhengyangZhang06/gmt-formalize/issues/581, https://github.com/ZhengyangZhang06/gmt-formalize/issues/582, https://github.com/ZhengyangZhang06/gmt-formalize/issues/584, https://github.com/ZhengyangZhang06/gmt-formalize/issues/586, https://github.com/ZhengyangZhang06/gmt-formalize/issues/588, https://github.com/ZhengyangZhang06/gmt-formalize/issues/590

## Lean problem

Declaration: `Submission.allard_regularity_theorem`

```lean
AllardRegularityTheorem
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

- Parent DAG node: `root`
- Child DAG node: `root.allard_regularity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 5, Theorem 5.2 and its printed proof (pp. 121-124: iteration of 4.5, Remark 4.6, Corollary 2.7, steps (1)-(11)). Corrections: (i) monotonicity with the correct constant Lambda = 4 p delta/(p-n) of Ch. 4, 4.2 (kappa = (p-n)/(4p)); (ii) Corollary 2.7 yields an operator-norm Lipschitz bound, while the graph-projection comparison (Gp) needs a Hilbert-Schmidt bound, so 2.7 is applied with L_* := L_0/sqrt(n), which gives |Df| <= sqrt(n) ||Df|| <= L_0; (iii) T_0 is taken to be the limit plane S(0), so that Du(0) = 0 holds without re-graphing. The printed proof fixes delta = delta(n,l,p) and takes gamma = delta/4; as the contract README notes, the rate C delta^(1/(2n+2)) at a gamma independent of delta needs more. This is supplied in Part III (not in the printed text): the conical excess at 0, which is O(delta) by monotonicity, bounds the height of the already established graph over a fixed fraction of B_rho(0) by radial integration; then Lemma A and the decay iteration give the rate.

Notation (contract). mu := V.weight = theta H^n restricted to M (M = V.carrier, theta = V.mult); spt V := V.support = U cap spt mu; p_x := V.tangentProj x and p_x^perp := I - p_x; |A| is the Hilbert-Schmidt norm (hsNorm), ||A|| the operator norm, ||A|| <= |A| <= sqrt(rank A) ||A||; B_s(y) is the closed ball and B^o_s(y) the open ball; omega_n := unitBallVolume n; K(z,s) := (s^(p-n) integral_{B_s(z)} |H|^p dmu)^(1/p) in [0,infinity] (the contract's scaledLpNorm); E(z,s,T) := s^-n integral_{B_s(z)} |p_x - p_T|^2 dmu (tiltExcess); kappa := (p-n)/(4p) > 0; a := 1/(2n+2). Under 2.3, if B_s(z) is contained in B_rho(0) then K(z,s)^p = s^(p-n) integral_{B_s(z)} |H|^p <= (s/rho)^(p-n) rho^(p-n) integral_{B_rho(0)} |H|^p, so K(z,s) <= (s/rho)^(1-n/p) delta <= delta.
Further notation: alpha' := 1 - n/p in (0,1); a = 1/(2n+2); for an l x n matrix A, graph A := {graphPoint(x, A x)} and p_{graph A} its orthogonal projection; for a linear isometry q, q(graph A) is the corresponding n-plane.

Siblings used: AffineApproximationLemma (2.5, constant C_A; we may assume C_A >= 1, enlarging it preserves both inequalities), LipschitzGraphCorollary (2.7, constant beta_7), TiltExcessDecayTheorem (4.5, constants eta, delta_45).

Facts used:
(F1) [Simon Ch. 3, Def. 1.7, Rem. 1.8, Thm. 1.9; contract tangentProj] For mu-a.e. x the approximate tangent space T_xM of M with respect to theta exists; at such x, p_x is the orthogonal projection onto the n-dimensional space T_xM, and Theta^n(mu,x) = theta(x) (Rem. 1.8(2)). The map x -> p_x is mu-measurable and bounded (|p_x - p_T|^2 <= 4n), so tilt integrals over compact subsets of U are finite: by Ch. 3, Rem. 1.3 and Rem. 1.8(1), M is covered up to an H^n-null set by countably many H^n-measurable pieces M_j contained in embedded C^1 submanifolds N_j, and for H^n-a.e. x in M_j the space T_xM exists and equals T_xN_j, which depends continuously on x in N_j; since T_xM is unique where theta(x) > 0 (SimonGMT HasWeightedApproximateTangentSpaceAt.unique), p_x agrees mu-a.e. with a Borel map. If Gamma is the graph of a Lipschitz map over (a subset of) an n-plane, then T_xM = T_x Gamma for H^n-a.e. x in M cap Gamma (Rem. 1.8(1)), and T_x Gamma is the range of the differential of the graph map at H^n-a.e. x in Gamma (Rademacher, Ch. 2, 1.4).
(F2) mu(R^(n+l) minus spt mu) = 0 and mu(R^(n+l) minus U) = 0, so mu-a.e. point lies in spt V; mu(K) < infinity for compact K in U; H^n(M minus spt V) = 0 (because mu(M minus spt V) = 0 and theta > 0 on M); spt V is relatively closed in U; if y in U minus spt V then mu(B^o_r(y)) = 0 for some r > 0.
(M) [Monotonicity: Simon Ch. 4, 4.1-4.10, with the coefficient in front of Lambda in 4.2 equal to kappa = (p-n)/(4p), the value required by the integration after 4.4 (cf. SimonGMT Chapter04 `lpMeanCurvatureKappa`, `LpAnnularCorrection`)]. Let y in R^(n+l) and R > 0 with B_R(y) in U and K(y,R) <= kappa Lambda for some Lambda > 0. (Under 2.3, whenever B_R(y) is contained in B_rho(0) we have K(y,R) <= delta, so Lambda := delta/kappa = 4 p delta/(p-n) is admissible; Lambda <= 1 as soon as delta <= kappa.) Then there are F : (0,R) -> (0,infinity) and numbers G(s,r) such that for all 0 < s <= r < R:
 (M.i) e^-Lambda <= F(r) <= e^Lambda and |F(r) - 1| <= (1/2) e^(Lambda/2) Lambda (r/R)^(1-n/p); if Lambda <= 1, then |F(r) - 1| <= Lambda (r/R)^(1-n/p) <= Lambda; F(r) -> 1 as r -> 0.
 (M.ii) Phi(r) - Phi(s) = G(s,r) integral_{B_r(y) minus B_s(y)} |p_x^perp(x - y)|^2 |x - y|^(-n-2) dmu(x), where Phi(t) := F(t) t^-n mu(B_t(y)) + F(t) - 1 and G(s,r) in [e^-Lambda, e^Lambda].
 (M.iii) Hence Phi is nondecreasing, Theta(y) := lim_{s -> 0} omega_n^-1 s^-n mu(B_s(y)) exists, and omega_n Theta(y) = lim_{s -> 0} Phi(s) <= Phi(r) for every r in (0,R); in particular mu({y}) = 0.
 (M.iv) [Ch. 4, 4.9 and 4.10(1), applied to V restricted to an open set W in U on which H is in L^p_loc] If theta >= 1 mu-a.e. and W is an open subset of U each point of which is the centre of a ball as above, then Theta >= 1 at every point of spt V cap W: Theta = theta >= 1 mu-a.e. by (F1), Theta is upper semicontinuous on W (4.9), so {x in W : Theta(x) < 1} is open and mu-null, hence disjoint from spt mu. Under 2.3 this applies to W = B^o_rho(0) (H is in L^p(B_rho(0)) since K(0,rho) <= delta < infinity).
 (M.v) If Lambda <= 1 and 0 < s <= r < R, then s^-n mu(B_s(y)) <= e^(2 Lambda) r^-n mu(B_r(y)) + 2 e^Lambda Lambda. [By (M.ii) Phi(s) <= Phi(r), so F(s) s^-n mu(B_s(y)) = Phi(s) - (F(s) - 1) <= F(r) r^-n mu(B_r(y)) + (F(r) - 1) + Lambda <= e^Lambda r^-n mu(B_r(y)) + 2 Lambda; divide by F(s) >= e^-Lambda.]
(P) [2.4 of the text, with explicit constants]. Assume 2.3 (AllardHypotheses H p delta rho) with delta <= min{1/8, kappa}, so Lambda := delta/kappa <= 1. Consider the smooth functions of t in [0, min{1/8, kappa}] (with Lambda_t := t/kappa)
 g_+(t) := e^(2 Lambda_t) (1 + t)(1 - 3t)^-n + 2 e^(Lambda_t) Lambda_t/omega_n,
 g_-(t) := e^(-Lambda_t) (1 - Lambda_t/omega_n),
 g_c(t) := e^(Lambda_t) (e^(Lambda_t) (1 + t)(1 - 3t)^-n - 1) + e^(Lambda_t) Lambda_t/omega_n.
Since g_+(0) = g_-(0) = 1 and g_c(0) = 0, there is C_P = C_P(n,p) >= 1 with g_+(t) <= 1 + C_P t, g_-(t) >= 1 - C_P t and g_c(t) <= C_P t on that interval. Put delta_P := min{1/8, kappa, 1/(2 C_P)}.
Claim. If delta <= delta_P, |y| <= 3 delta rho and 0 < s <= rho/2, then (P.i) mu(B_s(y)) <= (1 + C_P delta) omega_n s^n <= 2 omega_n s^n and Theta(y) <= 1 + C_P delta; if moreover y in spt V, then (P.ii) mu(B_s(y)) >= (1 - C_P delta) omega_n s^n >= omega_n s^n/2 and (P.iii) integral_{B_s(y)} |p_x^perp(x - y)|^2 |x - y|^(-n-2) dmu(x) <= C_P omega_n delta (integrand := 0 at x = y).
Proof. R_y := (1 - 3 delta) rho >= 5 rho/8 > rho/2 >= s, B_{R_y}(y) is contained in B_rho(0) (as |y| + R_y <= rho), so (M) applies at y with R = R_y and Lambda = delta/kappa <= 1, and mu(B_r(y)) <= mu(B_rho(0)) <= (1 + delta) omega_n rho^n for r < R_y. (P.i): for s <= r < R_y, (M.ii),(M.i) give F(s) s^-n mu(B_s(y)) = Phi(s) - (F(s) - 1) <= Phi(r) + Lambda <= e^Lambda r^-n mu(B_r(y)) + 2 Lambda; dividing by F(s) >= e^-Lambda and letting r -> R_y, omega_n^-1 s^-n mu(B_s(y)) <= g_+(delta); Theta(y) is the limit as s -> 0. (P.ii): Theta(y) >= 1 by (M.iv), so by (M.iii) F(s) s^-n mu(B_s(y)) >= omega_n - (F(s) - 1) >= omega_n - Lambda and s^-n mu(B_s(y)) >= e^-Lambda (omega_n - Lambda) = omega_n g_-(delta) (here omega_n - Lambda > 0 because g_-(delta) >= 1/2). (P.iii): for 0 < t < s <= r < R_y, (M.ii),(M.iii) give integral_{B_s(y) minus B_t(y)} |p_x^perp(x-y)|^2 |x-y|^(-n-2) dmu <= e^Lambda (Phi(r) - Phi(t)) <= e^Lambda (e^Lambda r^-n mu(B_r(y)) + Lambda - omega_n Theta(y)) <= e^Lambda (e^Lambda r^-n mu(B_r(y)) + Lambda - omega_n); let r -> R_y and t -> 0 (monotone convergence, mu({y}) = 0) to get <= omega_n g_c(delta).
(UD) [Upper Density Theorem, Simon Ch. 1, 3.6 with Remark 3.7(2), applied to the Borel regular measure mu, which is locally finite on U, and the set M, mu(U minus M) = 0]: limsup_{s -> 0} mu(B_s(x))/(omega_n s^n) = 0 for H^n-a.e. x in U minus M. Consequently, if W is open in U and Theta(x) >= 1 for every x in spt V cap W, then H^n((spt V cap W) minus M) = 0; together with (F2), mu restricted to W equals theta H^n restricted to spt V cap W, and on spt V cap W the null sets of mu and of H^n coincide.
Lemma A (L^1 form of the computation proving Lemma 2.1; valid for every V with generalized mean curvature H in U, no p needed). Let z in R^(n+l), r > 0 with B_r(z) contained in U, T an n-dimensional subspace and h >= 0 such that dist(x - z, T) <= h for every x in spt V cap B_r(z). Then
 integral_{B_{r/2}(z)} |p_x - p_T|^2 dmu <= 144 r^-2 integral_{B_r(z)} dist(x - z, T)^2 dmu + 4 h integral_{B_r(z)} |H| dmu.
Proof. Fix phi in C^infinity(R,[0,1]) with phi = 1 on (-infinity,1/2], phi = 0 on [1,infinity), |phi'| <= 3; put zeta(x) := phi(|x - z|/r) (smooth, since phi is constant near 0), x' := p_{T^perp}(x - z) (so |x'| = dist(x - z, T)) and X := zeta^2 x'. X is C^infinity, has compact support and tsupport X is contained in B_r(z), a subset of U, so X is admissible in the definition of generalized mean curvature, and X . H is mu-integrable because H is in L^1_loc(mu) on U. Since DX(x)v = zeta^2 p_{T^perp} v + 2 zeta (grad zeta . v) x', at every x where p_x is a rank-n orthogonal projection (mu-a.e. by (F1)) div_M X = trace(DX o p_x) = zeta^2 trace(p_{T^perp} p_x) + 2 zeta grad zeta . p_x x' = zeta^2 s + 2 zeta grad zeta . (p_x - p_T) x', where s := (1/2)|p_x - p_T|^2 (for rank-n orthogonal projections trace(p_{T^perp} p_x) = n - trace(p_T p_x) = (1/2)|p_x - p_T|^2) and p_T x' = 0. All integrands are bounded and measurable with support in B_r(z), which has finite measure (F2). The first variation identity gives integral zeta^2 s dmu = - integral 2 zeta grad zeta . (p_x - p_T) x' dmu - integral zeta^2 x' . H dmu. As |(p_x - p_T) x'| <= ||p_x - p_T|| |x'| <= sqrt(2s) |x'| and 2 sqrt(2s) zeta |grad zeta| |x'| <= (1/2) zeta^2 s + 4 |grad zeta|^2 |x'|^2, we get integral zeta^2 s dmu <= 8 integral |grad zeta|^2 |x'|^2 dmu + 2 integral zeta^2 |x'| |H| dmu. Finally zeta = 1 on B_{r/2}(z), 0 <= zeta <= 1, |grad zeta| <= 3/r, zeta = 0 off B_r(z), and |x'| <= h for mu-a.e. x in B_r(z) (such x lie in spt V by (F2)); hence (1/2) integral_{B_{r/2}(z)} |p_x - p_T|^2 dmu <= 72 r^-2 integral_{B_r(z)} |x'|^2 dmu + 2 h integral_{B_r(z)} |H| dmu.
(Leb) [Lebesgue-Besicovitch differentiation, Ch. 1, 3.23 / 3.16 ff.] For the Radon measure mu on B^o_rho(0) and the bounded mu-measurable map x -> p_x: for mu-a.e. zeta, mu(B_s(zeta))^-1 integral_{B_s(zeta)} |p_x - p_zeta|^2 dmu -> 0 as s -> 0.
(Area) [Ch. 2, Sect. 3] For an injective Lipschitz map F : A -> R^(n+l), A in R^n: integral_{F(A)} phi dH^n = integral_A phi(F) J_F dx for phi >= 0; for graph maps J_F >= 1; L^n-null sets of parameters correspond to H^n-null subsets of the graph.
(Rad) Rademacher [Ch. 2, 1.4]; a Lipschitz map whose a.e. derivative agrees a.e. on an open ball with a continuous map g is C^1 there with derivative g (mollify: f_eps -> f uniformly, D f_eps = (Df)_eps -> g locally uniformly).
(Gp) There is L_0 = L_0(n,l) in (0, 1/4] such that for l x n matrices A, B with |A|, |B| <= L_0: |A - B|^2 <= |p_{graph A} - p_{graph B}|^2 <= 3 |A - B|^2; in particular |A|^2 <= |p_{graph A} - p_{graph 0}|^2. Proof: Pi(A) := p_{graph A} = [[(I + A^T A)^-1, (I + A^T A)^-1 A^T], [A (I + A^T A)^-1, A (I + A^T A)^-1 A^T]] is real-analytic in A, DPi(0)[H] = [[0, H^T], [H, 0]] has |DPi(0)[H]|^2 = 2|H|^2, and |DPi(X) - DPi(0)| <= C_g |X| for |X| <= 1 (C_g = C_g(n,l)); by the mean value inequality |Pi(A) - Pi(B) - DPi(0)[A - B]| <= C_g max{|A|,|B|} |A - B|, so (sqrt 2 - C_g L_0)|A - B| <= |Pi(A) - Pi(B)| <= (sqrt 2 + C_g L_0)|A - B|; take C_g L_0 <= sqrt 3 - sqrt 2. Hilbert-Schmidt norms are invariant under conjugation by linear isometries, so the same holds for q(graph A), q(graph B).
(Nor) For an l x n matrix A and v in R^l: |p_{(graph A)^perp} graphPoint(0, v)| >= |v| (1 + ||A||^2)^(-1/2) (since |v| <= |v - A y| + ||A|| |y| <= (1 + ||A||^2)^(1/2) |graphPoint(-y, v - A y)| for all y).

Proof. Fix L_0 as in (Gp) and L_* := L_0/sqrt(n). C_1, C_2, ... depend only on n, l, p. delta_1 in (0, 1/4] is fixed at the end of Part II (depending only on n, l, p); delta_0 := delta_1, and gamma := delta_1/2048. Assume 2.3 with 0 < delta <= delta_1; then 2.3 also holds with delta_1 in place of delta, and in Parts I-II all siblings, (P) and E_* are used with the parameter delta_1 (we require delta_1 <= min{delta_45, delta_P}).

Part I (iteration of 4.5; book (1)-(7)).
1. Let xi in spt V cap B_{delta_1 rho}(0), sigma in (0, delta_1 rho/2] and S_0 an n-plane; E_*^(0) := E_*(xi, sigma, S_0). Applying 4.5 repeatedly (radii eta^j sigma <= delta_1 rho/2) gives n-planes S_j with E_*(xi, eta^j sigma, S_j) <= eta^(2 alpha' j) E_*^(0). Integrating |p_{S_j} - p_{S_(j-1)}|^2 <= 2|p_x - p_{S_j}|^2 + 2|p_x - p_{S_(j-1)}|^2 over B_{eta^j sigma}(xi) (measure >= omega_n (eta^j sigma)^n/2 by (P.ii)) and using E(xi, eta^j sigma, S_(j-1)) <= eta^-n E(xi, eta^(j-1) sigma, S_(j-1)) gives (book 4.6) |p_{S_j} - p_{S_(j-1)}|^2 <= (8/omega_n) eta^-n eta^(2 alpha' (j-1)) E_*^(0). Summing the geometric series, p_{S_j} converges to a rank-n orthogonal projection p_{S(xi)} (this set is closed) with
 |p_{S(xi)} - p_{S_k}|^2 <= C_II eta^(2 alpha' k) E_*^(0) for k >= 0, C_II := (8/omega_n) eta^-n (1 - eta^alpha')^-2, (5)
 and for 0 < s <= sigma (choose j with eta^(j+1) sigma < s <= eta^j sigma; use (P.i))
 E(xi, s, S(xi)) <= 2 (eta^j sigma/s)^n E(xi, eta^j sigma, S_j) + 4 omega_n |p_{S(xi)} - p_{S_j}|^2 <= C_III (s/sigma)^(2 alpha') E_*^(0), C_III := (2 eta^-n + 4 omega_n C_II) eta^(-2 alpha'). (7)
 The plane S(xi) does not depend on sigma and S_0: if E(xi,s,S) -> 0 and E(xi,s,S') -> 0 as s -> 0 then |p_S - p_S'|^2 <= (4/omega_n)(E(xi,s,S) + E(xi,s,S')) -> 0.

Part II (the Lipschitz graph is C^(1,alpha'); book (8)-(11)).
2. The sibling 2.5 at (0, 2 delta_1 rho) gives an n-plane T* with dist(x, T*) <= 2 C_A delta_1^a delta_1 rho on spt V cap B_{2 delta_1 rho}(0) and (K(0, 2 delta_1 rho) <= delta_1 <= delta_1^a) integral_{B_{delta_1 rho}(0)} |p_x - p_{T*}|^2 <= 2^n C_A^2 (C_A+1)^2 delta_1^(2a) (delta_1 rho)^n. For xi in spt V cap B_{delta_1 rho/2}(0), B_{delta_1 rho/2}(xi) is in B_{delta_1 rho}(0), so with sigma_1 := delta_1 rho/2: E_*(xi, sigma_1, T*) <= max{4^n C_A^2 (C_A+1)^2 delta_1^(2a), delta_1^-1 delta_1^2} <= C_2 delta_1^(2a) =: E_1, C_2 := 4^n C_A^2 (C_A+1)^2 + 1.
3. Apply Part I with sigma = sigma_1, S_0 = T* at every xi in spt V cap B_{delta_1 rho/2}(0), and put T_0 := S(0). By (5), |p_{S(xi)} - p_{T*}|^2 <= C_II E_1 for all such xi, and by (7), E(xi, s, S(xi)) <= C_III (s/sigma_1)^(2 alpha') E_1. Hence for xi in spt V cap B_{delta_1 rho/2}(0) and 0 < s <= sigma_1: E(xi, s, T_0) <= 2 E(xi, s, S(xi)) + 2 s^-n mu(B_s(xi)) |p_{S(xi)} - p_{T_0}|^2 <= (2 C_III + 16 omega_n C_II) E_1 =: C_3 E_1, and for x in spt V cap B_{2 delta_1 rho}(0): dist(x, T_0) <= dist(x, T*) + ||p_{T*} - p_{T_0}|| |x| <= K_1 delta_1^a (delta_1 rho), K_1 := 2 C_A + 2 (C_II C_2)^(1/2). Let q_0 be a linear isometry with rotatedPlane q_0 = T_0. We require delta_1 <= (beta_7 L_*)^(2n+2) and C_3 C_2 delta_1^(2a) <= beta_7^2 L_*^2. Then the sibling 2.7 with (delta_1, rho), L := L_*, K := K_1 and q := q_0 applies (its height and tilt hypotheses are the two estimates just proved) and gives f : R^n -> R^l, L_*-Lipschitz on B^n_{R_2}(0), R_2 := delta_1 rho/4, with
 spt V cap B_{R_2}(0) = Gamma cap B_{R_2}(0), Gamma := q_0 '' graphOver f (B^n_{R_2}(0)). (9)
 Write F(x') := q_0(graphPoint(x', f(x'))) and a(x) := first coordinates of q_0^-1 x. Where f is differentiable, ||Df|| <= L_* so |Df| <= sqrt(n) L_* = L_0 (Hilbert-Schmidt), as (Gp) requires.
4. Regularity of f.
 (a) Measure on the graph. By (M.iv), Theta >= 1 on spt V cap B^o_rho(0); by (UD) and (F2), mu restricted to B_{R_2}(0) equals theta H^n restricted to Gamma cap B_{R_2}(0), with theta >= 1 H^n-a.e. there; in particular integral_{Gamma cap A} phi dH^n <= integral_A phi dmu for phi >= 0 and A in B_{R_2}(0), and mu-null and H^n-null subsets of Gamma cap B_{R_2}(0) coincide.
 (b) Tangent planes. For H^n-a.e. zeta = F(z) in Gamma cap B_{R_2}(0), f is differentiable at z and T_zeta M = q_0(graph Df(z)) (F1). For mu-a.e. zeta in spt V cap B_{R_2/2}(0), p_zeta = p_{S(zeta)}: by (Leb) zeta is a Lebesgue point of x -> p_x, and |p_zeta - p_{S(zeta)}|^2 <= 2 mu(B_s(zeta))^-1 integral_{B_s(zeta)} |p_x - p_zeta|^2 dmu + (4/omega_n) E(zeta, s, S(zeta)) -> 0 as s -> 0 (by (P.ii) and (7)). By (a) and (Area), for L^n-a.e. z in B^n_{R_2/4}(0), with zeta := F(z) (|zeta| <= 2|z| <= R_2/2): q_0(graph Df(z)) = S(zeta).
 (c) Campanato inequality. For such z and 0 < s <= R_2/4, graph points over B^n_{s/2}(z) lie in B_s(zeta) (Lip f <= 1), and B_s(zeta) is in B_{3R_2/4}(0). By (Gp), (Area) (J_F >= 1), (a), (b) and (7):
 integral_{B^n_{s/2}(z)} |Df(x') - Df(z)|^2 dx' <= integral_{B^n_{s/2}(z)} |p_{F(x')} - p_{S(zeta)}|^2 dx' <= integral_{Gamma cap B_s(zeta)} |p_x - p_{S(zeta)}|^2 dH^n <= s^n E(zeta, s, S(zeta)) <= C_III s^n (s/sigma_1)^(2 alpha') E_1. (11)
 (d) Hoelder continuity. For a.e. x_1, x_2 in B^n_{R_2/16}(0), let d := |x_1 - x_2| (<= R_2/8) and m their midpoint; B^n_{d/2}(m) is contained in B^n_d(x_1) cap B^n_d(x_2). Averaging |Df(x_1) - Df(x_2)|^2 <= 2|Df(x) - Df(x_1)|^2 + 2|Df(x) - Df(x_2)|^2 over x in B^n_{d/2}(m) and applying (11) with s = 2d <= R_2/4 (and sigma_1 = 2 R_2): |Df(x_1) - Df(x_2)| <= C_5 (d/R_2)^alpha' E_1^(1/2), C_5 := (2^(2n+3) C_III/omega_n)^(1/2). By (Rad), f is C^1 on B^o_{R_2/16}(0) and this estimate holds for all x_1, x_2 there.
 (e) f(0) = 0, because 0 in spt V cap B_{R_2}(0) is in Gamma. Df(0) = 0: E(0, s, T_0) <= C_III (s/sigma_1)^(2 alpha') E_1 -> 0 (T_0 = S(0)); by (b), (Gp) and continuity of Df, for H^n-a.e. x in Gamma cap B_s(0), |p_x - p_{q_0(graph Df(0))}| <= sqrt 3 w(s) with w(s) := sup_{|x'| <= s} |Df(x') - Df(0)| -> 0, hence s^-n integral_{B_s(0)} |p_x - p_{q_0(graph Df(0))}|^2 dmu <= 6 omega_n w(s)^2 -> 0. Comparing on B_s(0) gives p_{T_0} = p_{q_0(graph Df(0))}, i.e. q_0(graph Df(0)) = T_0 = q_0(R^n x {0}), so Df(0) = 0.

Part III (the rate in delta).
5. Conical excess at 0, with the true delta (Lambda = delta/kappa <= 1 as delta <= delta_P <= kappa). (M) at 0 with R = rho, Theta(0) >= 1 (M.iv), and mu(B_r(0)) <= mu(B_rho(0)) <= (1 + delta) omega_n rho^n: for r < rho, integral_{B_r(0)} |p_x^perp x|^2 |x|^(-n-2) dmu <= e^Lambda (Phi(r) - omega_n) <= e^Lambda (e^Lambda r^-n mu(B_r(0)) + Lambda - omega_n); letting r -> rho, integral_{B^o_rho(0)} |p_x^perp x|^2 |x|^(-n-2) dmu <= omega_n [e^Lambda (e^Lambda (1 + delta) - 1) + e^Lambda Lambda/omega_n] <= C_6 delta (a smooth function of delta in [0, kappa] vanishing at 0). (C1)
6. Height. Let R_3 := R_2/16. For x' in B^o_{R_3}(0) put x := F(x'); since f(0) = 0 and ||Df|| <= L_* <= 1/4, |x| <= 2|x'|. For H^n-a.e. such x, T_xM = q_0(graph Df(x')), q_0(graphPoint(x', Df(x') x')) is in T_xM, and x - q_0(graphPoint(x', Df(x') x')) = q_0(graphPoint(0, v)), v := f(x') - Df(x') x'; by (Nor), |p_x^perp x| >= |v|/2. With (a), (Area) and (C1):
 integral_{B^n_{R_3}} |f(x') - Df(x') x'|^2 |x'|^(-n-2) dx' <= 4 * 2^(n+2) integral_{Gamma cap B_{2 R_3}(0)} |p_x^perp x|^2 |x|^(-n-2) dH^n <= 2^(n+4) C_6 delta.
 Polar coordinates x' = r w (w in S^(n-1) with H^(n-1); for n = 1, S^0 = {-1, 1} with counting measure): W(r,w) := f(rw)/r satisfies d/dr W(r,w) = (Df(rw) rw - f(rw))/r^2, hence integral_{S^(n-1)} integral_0^(R_3) r |d/dr W|^2 dr dw <= 2^(n+4) C_6 delta. Let r_1 := delta^(1/alpha') R_3. By 4(d) and Df(0) = 0, f(0) = 0: |W(r,w)| <= sup_{|x'| <= r_1} |Df(x')| <= C_5 (r_1/R_2)^alpha' E_1^(1/2) <= C_5 delta for r <= r_1 (E_1 <= 1). For r_1 <= r < R_3, D_r(w) := W(r,w) - W(r_1,w) satisfies, by Cauchy-Schwarz, integral_S |D_r|^2 <= log(R_3/r_1) 2^(n+4) C_6 delta = (2^(n+4) C_6/alpha') delta log(1/delta). D_r is 2-Lipschitz on S^(n-1) (|W(r,w) - W(r,w')| <= ||Df|| |w - w'| <= |w - w'|) and |D_r| <= 2. If n >= 2 and |D_r(w_0)| = m, then |D_r| >= m/2 on the cap S^(n-1) cap B_{m/4}(w_0), whose H^(n-1)-measure is >= c_n m^(n-1); hence c_n m^(n+1)/4 <= integral_S |D_r|^2 (for n = 1 directly m^2 <= integral_S |D_r|^2). So sup |D_r| <= C (delta log(1/delta))^(1/(n+1)) <= C' delta^a (since delta^a log(1/delta)^(2a) is bounded on (0,1)). Hence
 |f(x')| <= C_7 delta^a |x'| for x' in B^o_{R_3}(0), and dist(x, T_0) = |f(a(x))| <= C_7 delta^a R_3 for x in spt V cap B^o_{R_3}(0). (H)
7. Tilt at a fixed scale. Let zeta in spt V cap B_{R_3/4}(0) and r := R_3/2. Points x in spt V cap B_r(zeta) lie in spt V cap B_{3R_3/4}(0), so by (H) dist(x - zeta, T_0) <= dist(x, T_0) + dist(zeta, T_0) <= 2 C_7 delta^a R_3 =: h. Lemma A, (P.i) (mu(B_r(zeta)) <= 2 omega_n r^n) and Hoelder (integral_{B_r(zeta)} |H| <= delta rho^(n/p - 1) (2 omega_n r^n)^(1 - 1/p) <= 2 omega_n^(1-1/p) delta r^(n-1)) give
 E(zeta, R_3/4, T_0) = (r/2)^-n integral_{B_{r/2}(zeta)} |p_x - p_{T_0}|^2 dmu <= 2^n [288 omega_n (h/r)^2 + 8 omega_n^(1-1/p) (h/r) delta] <= C_9 delta^(2a) (h/r = 4 C_7 delta^a, delta <= delta^a).
8. Decay with the rate. For zeta in spt V cap B_{R_3/4}(0), Part I with sigma' := R_3/4 (<= delta_1 rho/2) and S_0 := T_0 applies, with E_*(zeta, sigma', T_0) <= C_9 delta^(2a) + delta_1^-1 delta^2 <= C_10 delta^(2a) (K(zeta, sigma') <= delta). It gives the limit plane S(zeta) with |p_{S(zeta)} - p_{T_0}|^2 <= C_II C_10 delta^(2a) and E(zeta, s, S(zeta)) <= C_III C_10 (s/sigma')^(2 alpha') delta^(2a) for 0 < s <= sigma'. Repeating 4(b)-(d) with E_1 replaced by C_10 delta^(2a) and sigma_1 by sigma': for a.e. z in B^n_{R_3/16}(0) (then zeta = F(z) is in spt V cap B_{R_3/8}(0)) and 0 < s <= R_3/16, integral_{B^n_{s/2}(z)} |Df - Df(z)|^2 <= C_III C_10 s^n (s/sigma')^(2 alpha') delta^(2a); and for x_1, x_2 in B^n_{R_3/16}(0) with d := |x_1 - x_2| <= R_3/32, averaging over B^n_{d/2}(midpoint) and using this with s = 2d <= R_3/16 gives |Df(x_1) - Df(x_2)| <= C_11 (d/R_3)^alpha' delta^a, C_11 := (2^(2n+2) C_III C_10/omega_n)^(1/2) 8^alpha' (first for a.e. pairs, then for all by continuity). Also, for a.e. z in B^n_{R_3/16}(0), by (Gp) with B = 0, |Df(z)| <= |p_{q_0(graph Df(z))} - p_{T_0}| = |p_{S(F(z))} - p_{T_0}| <= (C_II C_10)^(1/2) delta^a, hence for all such z by continuity. For x_1, x_2 in B^n_{R_3/32}(0) we have d <= R_3/16; if d > R_3/32 we use |Df(x_1) - Df(x_2)| <= 2 (C_II C_10)^(1/2) delta^a <= 2 (C_II C_10)^(1/2) 32^alpha' (d/R_3)^alpha' delta^a. So on B^n_{R_3/32}(0): sup |Df| <= C_12 delta^a and |Df(x_1) - Df(x_2)| <= C_12 (|x_1 - x_2|/R_3)^alpha' delta^a, C_12 := max{C_11, 2 (C_II C_10)^(1/2) 32^alpha'}.
9. Conclusion. Put gamma := R_3/(32 rho) = delta_1/2048 in (0,1), delta_0 := delta_1 in (0,1), q := q_0, u := f. u is C^1 on the open ball B^o_{R_2/16}(0), which contains the closed ball B^n_{gamma rho}(0); so u is ContDiffOn 1 on the closed ball and fderivWithin there equals Du. u(0) = 0 and Du(0) = 0 (step 4(e)). Intersecting (9) with B_{gamma rho}(0), and noting that q_0(graphPoint(x', u(x'))) in B_{gamma rho}(0) forces |x'| <= gamma rho, gives spt V cap B_{gamma rho}(0) = q '' graphOver u (B^n_{gamma rho}(0)) cap B_{gamma rho}(0). On B^n_{gamma rho}(0): rho^-1 sup|u| <= rho^-1 C_7 delta^a gamma rho <= C_7 delta^a by (H); sup |Du| (Hilbert-Schmidt) <= C_12 delta^a; rho^alpha' sup_{x != y} |Du(x) - Du(y)|/|x - y|^alpha' <= C_12 (rho/R_3)^alpha' delta^a = C_12 (64/delta_1)^alpha' delta^a. All suprema are finite reals, so scaledC1AlphaNorm u (B^n_{gamma rho}(0)) (1 - n/p) rho <= ofReal(C delta^(1/(2n+2))) with C := C_7 + C_12 + C_12 (64/delta_1)^alpha'. Finally delta_1 in (0, 1/4] is chosen (depending only on n, l, p) with delta_1 <= min{delta_45, delta_P, (beta_7 L_*)^(2n+2)}, C_3 C_2 delta_1^(2a) <= beta_7^2 L_*^2 and E_1 = C_2 delta_1^(2a) <= 1; the constants C_II, C_III (from eta) and C_3, K_1 do not depend on delta_1, so these requirements are consistent.

## Key steps

1. Iterate 4.5 to get limit planes S(xi) with decay (7)
2. T_0 := S(0); 2.7 with L_* = L_0/sqrt(n) gives a Lipschitz graph with Hilbert-Schmidt |Df| <= L_0
3. Campanato estimate via (Gp) makes f C^{1,alpha'} with Df(0) = 0
4. Conical excess at 0 is O(delta) by monotonicity with Lambda = 4 p delta/(p-n)
5. Radial integration bounds the height by C delta^(1/(2n+2)) |x'|
6. Lemma A gives tilt O(delta^(1/(n+1))) at a fixed scale
7. Restarted decay iteration gives the C^{1,alpha'} rate; gamma = delta_1/2048

## Reference use

### local-project

Queries:
- `rg -l 'TiltExcessHeightEstimate|AffineApproximationLemma|LipschitzApproximationLemma|LipschitzGraphCorollary|HarmonicApproximationLemma|TiltExcessDecayTheorem|AllardRegularityTheorem|AllardRegularityAnyRadius|ConicalApproximationTheorem|DensityOneRegularity|DensityOneHigherRegularity|RegularSetOpenDense' <snapshot>`
- `for pat in Rellich Kondrachov Weyl Campanato Kirszbraun '[Cc]oarea' '[Vv]arifold' Allard Schauder 'Poincare_inequality|poincare_inequality'; do rg -l $pat <snapshot>/mathlib/Mathlib | wc -l; done`
- `rg -n 'def HarmonicOnNhd|def HarmonicAt|theorem mk_ball' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic`
- `rg -n 'theorem LipschitzOnWith.extend_real|lipschitzExtensionConstant' <snapshot>/mathlib/Mathlib`
- `rg -l 'exists_disjoint_subfamily_covering_enlargement|Besicovitch|Rademacher|lintegral_image_eq_lintegral_abs_det_fderiv_mul' <snapshot>/mathlib/Mathlib`
- `rg -n 'def lpMeanCurvatureKappa|structure LpAnnularCorrection|exists_lpAnnularCorrection|one_le_stationaryDensityReal_of_mem_support_lp|fiveTimes|lipschitz_extension_real_optimal|rademacher_ae_differentiableAt|injective_area_formula_lipschitz_simon|harmonicComparison_energy_le_sixthPower|HasWeightedApproximateTangentSpaceAt.unique' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -c sorry .lake/packages/simongmt/Poincare/SimonGMT`
- `lake env lean /tmp/gmt-ch05-v2-check/Check.lean (Contract.lean lines 1-460, then namespace Submission with the 12 child declarations, then the root assembly)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/SobolevCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter05/HarmonicEnergy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/gmt-ch05-v2-check/Check.lean`

Snapshot pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json).

No prior proofs: the 12 conjunct names occur only in project/GMT/Ch05/{Contract,Submission}.lean and README.md.

No-match searches in mathlib/Mathlib (0 files each): Rellich, Kondrachov, Campanato, Kirszbraun, coarea, varifold, Allard, Poincare_inequality. 'Weyl' matches only Lie-algebra and root-system files, and 'Schauder' only Schauder-basis files (l2Space.lean, Normed/Module/Bases.lean). So Mathlib has no Weyl lemma for harmonic functions and no Schauder PDE theory.

Usable Mathlib items:
- HarmonicAt and HarmonicOnNhd (Harmonic/Basic.lean:41,48).
- LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308) and lipschitzExtensionConstant (FiniteDimension.lean:194).
- Vitali and Besicovitch coverings.
- Rademacher (Analysis/Calculus/Rademacher.lean).
- Change of variables (MeasureTheory/Function/Jacobian.lean).

The pinned simongmt package lies outside the snapshot; 'rg -c sorry' finds no matches. It provides:
- lpMeanCurvatureKappa = (p-n)/(4p) (Chapter04/LpMeanCurvature.lean:76) and LpAnnularCorrection (Chapter04/LpAnnular.lean:335). These confirm the corrected monotonicity used in all revised child proofs: Lambda = 4 p delta/(p-n), factor bounds e^(-Lambda) <= F <= e^Lambda, error |F-1| <= (e^(Lambda/2)/2) Lambda (rho/R)^(1-n/p), and |F-1| <= Lambda (rho/R)^(1-n/p) when Lambda <= 1.
- one_le_stationaryDensityReal_of_mem_support_lp (LpLowerDensity.lean:43).
- Chapter01.exists_fiveTimesCovering (used at Chapter04/SobolevCovering.lean:39).
- lipschitz_extension_real_optimal and rademacher_ae_differentiableAt (Chapter02/Lipschitz.lean:170,192).
- injective_area_formula_lipschitz_simon (Chapter02/AreaLipschitz.lean:126).
- HasWeightedApproximateTangentSpaceAt.unique (Chapter03/Rectifiable.lean:345).
- harmonicComparison_energy_le_sixthPower (Chapter05/HarmonicEnergy.lean:94).
The Chapter04 results are stated for the stronger Chapter04.RectifiableVarifold, which stores the tangent field as data, so reuse needs a bridge via Ch. 3, 1.9 and axiom checks.

Lean check (Check.lean): all 12 child types elaborate in the contract scope, and the root assembly has exactly the type of main_theorem. The only warnings are sorry warnings for the placeholder child declarations.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/5480

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
