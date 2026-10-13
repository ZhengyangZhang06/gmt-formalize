<!-- theorem-id: gmt-ch05/root.allard_any_radius-a1 -->

## Theorem `Submission.allard_regularity_any_radius`

For n >= 1, l, p > n and every gamma in (0,1) there are delta_0 in (0,1) and C, depending on gamma,n,l,p, such that for every open U, V with generalized mean curvature H, 0 < delta <= delta_0 and rho with AllardHypotheses H p delta rho, AllardConclusion V p delta rho gamma C holds (the conclusion of Theorem 5.2 on the ball of radius gamma rho, with constant C).

Node: `root.allard_any_radius-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/119, https://github.com/ZhengyangZhang06/gmt-formalize/issues/123, https://github.com/ZhengyangZhang06/gmt-formalize/issues/118

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/610, https://github.com/ZhengyangZhang06/gmt-formalize/issues/611, https://github.com/ZhengyangZhang06/gmt-formalize/issues/612, https://github.com/ZhengyangZhang06/gmt-formalize/issues/614, https://github.com/ZhengyangZhang06/gmt-formalize/issues/615, https://github.com/ZhengyangZhang06/gmt-formalize/issues/618, https://github.com/ZhengyangZhang06/gmt-formalize/issues/620, https://github.com/ZhengyangZhang06/gmt-formalize/issues/622, https://github.com/ZhengyangZhang06/gmt-formalize/issues/624, https://github.com/ZhengyangZhang06/gmt-formalize/issues/627, https://github.com/ZhengyangZhang06/gmt-formalize/issues/631, https://github.com/ZhengyangZhang06/gmt-formalize/issues/634

## Lean problem

Declaration: `Submission.allard_regularity_any_radius`

```lean
AllardRegularityAnyRadius
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
- Child DAG node: `root.allard_any_radius-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 5, Remark 5.3 (p. 122) announces this improvement of Theorem 5.2 'in the next section' (Section 6, 'Conical approximation, extension of Allard's theorem'); the book prints the conical approximation Theorem 6.1 but no proof of 5.3. The proof below follows the announced route: 6.1 and monotonicity give mass-ratio pinching at every point of spt V cap B_{gamma_b rho}(0); Theorem 5.2 then gives local graphs at a fixed scale; 6.1 again forces spt V into a thin cone around the tangent plane T_0 at 0, so the local graphs patch to one graph over T_0; the rate comes from the conical excess at 0 (O(delta) by monotonicity), radial integration, Lemma A and the decay iteration of 4.5. Monotonicity is used with the correct constant Lambda = 4 p delta/(p-n) of Ch. 4, 4.2 (kappa = (p-n)/(4p)).

Notation (contract). mu := V.weight = theta H^n restricted to M (M = V.carrier, theta = V.mult); spt V := V.support = U cap spt mu; p_x := V.tangentProj x and p_x^perp := I - p_x; |A| is the Hilbert-Schmidt norm (hsNorm), ||A|| the operator norm, ||A|| <= |A| <= sqrt(rank A) ||A||; B_s(y) is the closed ball and B^o_s(y) the open ball; omega_n := unitBallVolume n; K(z,s) := (s^(p-n) integral_{B_s(z)} |H|^p dmu)^(1/p) in [0,infinity] (the contract's scaledLpNorm); E(z,s,T) := s^-n integral_{B_s(z)} |p_x - p_T|^2 dmu (tiltExcess); kappa := (p-n)/(4p) > 0; a := 1/(2n+2). Under 2.3, if B_s(z) is contained in B_rho(0) then K(z,s)^p = s^(p-n) integral_{B_s(z)} |H|^p <= (s/rho)^(p-n) rho^(p-n) integral_{B_rho(0)} |H|^p, so K(z,s) <= (s/rho)^(1-n/p) delta <= delta.
Further notation: alpha' := 1 - n/p; a = 1/(2n+2); for an l x n matrix A, graph A := {graphPoint(x, A x)}; P_0 := p_{T_0}, Q_0 := I - P_0 once T_0 is fixed.

Siblings used: AllardRegularityTheorem (5.2: constants delta_7, gamma_7, C_7), ConicalApproximationTheorem (6.1: we use its constant C_9 := C(n, l, Lambda~) for Lambda~ := 2 omega_n), TiltExcessDecayTheorem (4.5: constants eta, delta_6). We may assume C_7, C_9 >= 1 (enlarging them preserves the sibling conclusions, the multiplied quantities being nonnegative).

Facts used:
(F1) [Simon Ch. 3, Def. 1.7, Rem. 1.8, Thm. 1.9; contract tangentProj] For mu-a.e. x the approximate tangent space T_xM of M with respect to theta exists; at such x, p_x is the orthogonal projection onto the n-dimensional space T_xM, and Theta^n(mu,x) = theta(x) (Rem. 1.8(2)). The map x -> p_x is mu-measurable and bounded (|p_x - p_T|^2 <= 4n), so tilt integrals over compact subsets of U are finite: by Ch. 3, Rem. 1.3 and Rem. 1.8(1), M is covered up to an H^n-null set by countably many H^n-measurable pieces M_j contained in embedded C^1 submanifolds N_j, and for H^n-a.e. x in M_j the space T_xM exists and equals T_xN_j, which depends continuously on x in N_j; since T_xM is unique where theta(x) > 0 (SimonGMT HasWeightedApproximateTangentSpaceAt.unique), p_x agrees mu-a.e. with a Borel map. If Gamma is the graph of a Lipschitz map over (a subset of) an n-plane, then T_xM = T_x Gamma for H^n-a.e. x in M cap Gamma (Rem. 1.8(1)), and T_x Gamma is the range of the differential of the graph map at H^n-a.e. x in Gamma (Rademacher, Ch. 2, 1.4).
(F2) mu(R^(n+l) minus spt mu) = 0 and mu(R^(n+l) minus U) = 0, so mu-a.e. point lies in spt V; mu(K) < infinity for compact K in U; H^n(M minus spt V) = 0 (because mu(M minus spt V) = 0 and theta > 0 on M); spt V is relatively closed in U; if y in U minus spt V then mu(B^o_r(y)) = 0 for some r > 0.
(M) [Monotonicity: Simon Ch. 4, 4.1-4.10, with the coefficient in front of Lambda in 4.2 equal to kappa = (p-n)/(4p), the value required by the integration after 4.4 (cf. SimonGMT Chapter04 `lpMeanCurvatureKappa`, `LpAnnularCorrection`)]. Let y in R^(n+l) and R > 0 with B_R(y) in U and K(y,R) <= kappa Lambda for some Lambda > 0. (Under 2.3, whenever B_R(y) is contained in B_rho(0) we have K(y,R) <= delta, so Lambda := delta/kappa = 4 p delta/(p-n) is admissible; Lambda <= 1 as soon as delta <= kappa.) Then there are F : (0,R) -> (0,infinity) and numbers G(s,r) such that for all 0 < s <= r < R:
 (M.i) e^-Lambda <= F(r) <= e^Lambda and |F(r) - 1| <= (1/2) e^(Lambda/2) Lambda (r/R)^(1-n/p); if Lambda <= 1, then |F(r) - 1| <= Lambda (r/R)^(1-n/p) <= Lambda; F(r) -> 1 as r -> 0.
 (M.ii) Phi(r) - Phi(s) = G(s,r) integral_{B_r(y) minus B_s(y)} |p_x^perp(x - y)|^2 |x - y|^(-n-2) dmu(x), where Phi(t) := F(t) t^-n mu(B_t(y)) + F(t) - 1 and G(s,r) in [e^-Lambda, e^Lambda].
 (M.iii) Hence Phi is nondecreasing, Theta(y) := lim_{s -> 0} omega_n^-1 s^-n mu(B_s(y)) exists, and omega_n Theta(y) = lim_{s -> 0} Phi(s) <= Phi(r) for every r in (0,R); in particular mu({y}) = 0.
 (M.iv) [Ch. 4, 4.9 and 4.10(1), applied to V restricted to an open set W in U on which H is in L^p_loc] If theta >= 1 mu-a.e. and W is an open subset of U each point of which is the centre of a ball as above, then Theta >= 1 at every point of spt V cap W: Theta = theta >= 1 mu-a.e. by (F1), Theta is upper semicontinuous on W (4.9), so {x in W : Theta(x) < 1} is open and mu-null, hence disjoint from spt mu. Under 2.3 this applies to W = B^o_rho(0) (H is in L^p(B_rho(0)) since K(0,rho) <= delta < infinity).
 (M.v) If Lambda <= 1 and 0 < s <= r < R, then s^-n mu(B_s(y)) <= e^(2 Lambda) r^-n mu(B_r(y)) + 2 e^Lambda Lambda. [By (M.ii) Phi(s) <= Phi(r), so F(s) s^-n mu(B_s(y)) = Phi(s) - (F(s) - 1) <= F(r) r^-n mu(B_r(y)) + (F(r) - 1) + Lambda <= e^Lambda r^-n mu(B_r(y)) + 2 Lambda; divide by F(s) >= e^-Lambda.]
(UD) [Upper Density Theorem, Simon Ch. 1, 3.6 with Remark 3.7(2), applied to the Borel regular measure mu, which is locally finite on U, and the set M, mu(U minus M) = 0]: limsup_{s -> 0} mu(B_s(x))/(omega_n s^n) = 0 for H^n-a.e. x in U minus M. Consequently, if W is open in U and Theta(x) >= 1 for every x in spt V cap W, then H^n((spt V cap W) minus M) = 0; together with (F2), mu restricted to W equals theta H^n restricted to spt V cap W, and on spt V cap W the null sets of mu and of H^n coincide.
Lemma A (L^1 form of the computation proving Lemma 2.1; valid for every V with generalized mean curvature H in U, no p needed). Let z in R^(n+l), r > 0 with B_r(z) contained in U, T an n-dimensional subspace and h >= 0 such that dist(x - z, T) <= h for every x in spt V cap B_r(z). Then
 integral_{B_{r/2}(z)} |p_x - p_T|^2 dmu <= 144 r^-2 integral_{B_r(z)} dist(x - z, T)^2 dmu + 4 h integral_{B_r(z)} |H| dmu.
Proof. Fix phi in C^infinity(R,[0,1]) with phi = 1 on (-infinity,1/2], phi = 0 on [1,infinity), |phi'| <= 3; put zeta(x) := phi(|x - z|/r) (smooth, since phi is constant near 0), x' := p_{T^perp}(x - z) (so |x'| = dist(x - z, T)) and X := zeta^2 x'. X is C^infinity, has compact support and tsupport X is contained in B_r(z), a subset of U, so X is admissible in the definition of generalized mean curvature, and X . H is mu-integrable because H is in L^1_loc(mu) on U. Since DX(x)v = zeta^2 p_{T^perp} v + 2 zeta (grad zeta . v) x', at every x where p_x is a rank-n orthogonal projection (mu-a.e. by (F1)) div_M X = trace(DX o p_x) = zeta^2 trace(p_{T^perp} p_x) + 2 zeta grad zeta . p_x x' = zeta^2 s + 2 zeta grad zeta . (p_x - p_T) x', where s := (1/2)|p_x - p_T|^2 (for rank-n orthogonal projections trace(p_{T^perp} p_x) = n - trace(p_T p_x) = (1/2)|p_x - p_T|^2) and p_T x' = 0. All integrands are bounded and measurable with support in B_r(z), which has finite measure (F2). The first variation identity gives integral zeta^2 s dmu = - integral 2 zeta grad zeta . (p_x - p_T) x' dmu - integral zeta^2 x' . H dmu. As |(p_x - p_T) x'| <= ||p_x - p_T|| |x'| <= sqrt(2s) |x'| and 2 sqrt(2s) zeta |grad zeta| |x'| <= (1/2) zeta^2 s + 4 |grad zeta|^2 |x'|^2, we get integral zeta^2 s dmu <= 8 integral |grad zeta|^2 |x'|^2 dmu + 2 integral zeta^2 |x'| |H| dmu. Finally zeta = 1 on B_{r/2}(z), 0 <= zeta <= 1, |grad zeta| <= 3/r, zeta = 0 off B_r(z), and |x'| <= h for mu-a.e. x in B_r(z) (such x lie in spt V by (F2)); hence (1/2) integral_{B_{r/2}(z)} |p_x - p_T|^2 dmu <= 72 r^-2 integral_{B_r(z)} |x'|^2 dmu + 2 h integral_{B_r(z)} |H| dmu.
(Leb) [Lebesgue-Besicovitch differentiation] For mu-a.e. zeta in B^o_rho(0): mu(B_s(zeta))^-1 integral_{B_s(zeta)} |p_x - p_zeta|^2 dmu -> 0 as s -> 0.
(Area) [Ch. 2, Sect. 3] area formula for injective Lipschitz (graph) maps, J >= 1; null sets of parameters correspond to H^n-null subsets of the graph.
(Gp) There is L_0 = L_0(n,l) in (0,1/4] with |A - B|^2 <= |p_{graph A} - p_{graph B}|^2 <= 3|A - B|^2 for |A|, |B| <= L_0 (Hilbert-Schmidt): Pi(A) := p_{graph A} = [[(I + A^T A)^-1, (I + A^T A)^-1 A^T], [A (I + A^T A)^-1, A (I + A^T A)^-1 A^T]] is real-analytic, DPi(0)[H] = [[0, H^T],[H, 0]] has norm sqrt 2 |H|, and |DPi(X) - DPi(0)| <= C_g |X| for |X| <= 1; choose C_g L_0 <= sqrt 3 - sqrt 2. The same holds after conjugation by a linear isometry.
(Ang) For every l x n matrix A: ||p_{graph A} - p_{graph 0}|| >= ||A|| (1 + ||A||^2)^(-1/2) (take a unit x with |Ax| = ||A||; v := graphPoint(x, Ax)/(1 + |Ax|^2)^(1/2) is a unit vector of graph A and (p_{graph A} - p_{graph 0}) v = graphPoint(0, Ax)/(1 + |Ax|^2)^(1/2)).
(Nor) |p_{(graph A)^perp} graphPoint(0, v)| >= |v| (1 + ||A||^2)^(-1/2).
(Inv) Translations, linear isometries and dilations: for c in U and R > 0, V - c and the dilation V~ := eta_{0,R #} V (carrier M/R, multiplicity theta(R .)) are contract varifolds in U - c resp. U/R; mu~(A) = R^-n mu(R A), tangent planes are transported, the generalized mean curvature of V~ is H~(x) = R H(R x), r^(1-n) integral_{B_r(0)} |H~| dmu~ = (rR)^(1-n) integral_{B_{rR}(0)} |H| dmu, and spt V~ = (spt V)/R.
(Iter) [iteration of 4.5] If V' satisfies 2.3 at (0, s_1) with parameter delta' <= delta_6, sigma in (0, delta' s_1/2], S_0 is an n-plane, and c_l omega_n s^n <= mu'(B_s(0)) <= c_u omega_n s^n for 0 < s <= sigma, then there is an n-plane S with |p_S - p_{S_0}|^2 <= C_II E_*' and E'(0, s, S) <= C_III (s/sigma)^(2 alpha') E_*' for 0 < s <= sigma, where E_*' := E_*'(0, sigma, S_0) (E_* with parameter delta') and C_II, C_III depend only on n, l, p, c_l, c_u. Proof: 4.5 gives S_j with E_*'(0, eta^j sigma, S_j) <= eta^(2 alpha' j) E_*'; integrating |p_{S_j} - p_{S_(j-1)}|^2 <= 2|p_x - p_{S_j}|^2 + 2|p_x - p_{S_(j-1)}|^2 over B_{eta^j sigma}(0) gives |p_{S_j} - p_{S_(j-1)}|^2 <= (4/(c_l omega_n)) eta^-n eta^(2 alpha' (j-1)) 2 E_*'; the geometric series gives the limit S with |p_S - p_{S_k}|^2 <= C_II eta^(2 alpha' k) E_*', and for eta^(j+1) sigma < s <= eta^j sigma, E'(0,s,S) <= 2 eta^-n eta^(2 alpha' j) E_*' + 4 c_u omega_n C_II eta^(2 alpha' j) E_*' <= C_III (s/sigma)^(2 alpha') E_*'. If E'(0,s,S) -> 0 and E'(0,s,S') -> 0 then S = S' (compare on B_s(0)).

Proof. Fix gamma in (0,1); put gamma_b := (1 + gamma)/2, gamma_a := (1 + 3 gamma)/4, gammahat := (gamma + gamma_a)/2 (so gamma < gammahat < gamma_a < gamma_b < 1, gamma_b - gamma_a = (1 - gamma)/4), theta_0 := (1 - gamma_b)/4 = (1 - gamma)/8 in (0, 1/8], gamma_7' := min{gamma_7, 1/4}. C_gamma denotes constants depending only on n, l, p, gamma. Assume 2.3 with 0 < delta <= delta_0(gamma), where delta_0 in (0,1) is the minimum of the finitely many positive thresholds required below; in particular delta <= kappa, so every application of (M) at a centre y with B_R(y) in B_rho(0) has Lambda = delta/kappa <= 1, and K(y, R) <= delta.

1. Centre 0 and density bounds.
 (1a) For 0 < r <= rho: |omega_n^-1 r^-n mu(B_r(0)) - 1| <= C_1 delta. [Upper: for r < r' < rho, (M.v) at 0 with R = rho gives omega_n^-1 r^-n mu(B_r(0)) <= e^(2 Lambda) omega_n^-1 r'^-n mu(B_rho(0)) + 2 e^Lambda Lambda/omega_n, and letting r' -> rho, <= e^(2 Lambda)(1 + delta) + 2 e^Lambda Lambda/omega_n; for r = rho it is <= 1 + delta by 2.3. Lower: Theta(0) >= 1 by (M.iv) (0 in spt V), so by (M.iii) omega_n^-1 r^-n mu(B_r(0)) >= e^-Lambda (1 - Lambda/omega_n) for r < rho, and the case r = rho follows by monotonicity of mu. Both bounds are smooth functions of delta equal to 1 at delta = 0.]
 (1b) r^(1-n) integral_{B_r(0)} |H| dmu <= C_1 delta for 0 < r <= rho: by Hoelder and (1a), integral_{B_r(0)} |H| <= delta rho^(n/p - 1) (2 omega_n r^n)^(1 - 1/p).
 (1c) integral_{B^o_rho(0)} |p_x^perp x|^2 |x|^(-n-2) dmu <= C_1 delta [(M.ii),(M.iii) at 0: for r < rho the integral over B_r(0) is <= e^Lambda (e^Lambda r^-n mu(B_r(0)) + Lambda - omega_n); let r -> rho].
 (1d) If |y| <= gamma_b rho and 0 < s <= (1 - gamma_b) rho/2, then mu(B_s(y)) <= C_1' omega_n s^n, C_1' := 2 e^2 (1 - gamma_b)^-n + 2e/omega_n; if moreover y in spt V, then mu(B_s(y)) >= omega_n s^n/2. [(M) at y with R = (1 - gamma_b) rho, B_R(y) in B_rho(0): upper bound by (M.v) with r -> R and mu(B_r(y)) <= mu(B_rho(0)) <= 2 omega_n rho^n; lower bound: Theta(y) >= 1 by (M.iv), so by (M.iii) F(s) s^-n mu(B_s(y)) >= omega_n - (F(s) - 1) >= omega_n - Lambda and s^-n mu(B_s(y)) >= e^-Lambda (omega_n - Lambda) >= omega_n/2 for delta small.]

2. Pinching at every point. Let eps_1 in (0, 1/4] (fixed in step 6, depending only on n, l, p), kappa_0 := min{1/4, eps_1/(8n)} (so (1 - kappa_0)^-n <= 1 + eps_1/2) and s_* := kappa_0 theta_0 rho/2. Claim: for delta small (depending on gamma, eps_1), omega_n^-1 s_*^-n mu(B_{s_*}(y)) <= 1 + eps_1 for every y in spt V cap B_{gamma_b rho}(0).
 (a) If |y| <= kappa_0 rho: (M.v) at y with R := (1 - kappa_0) rho (B_R(y) in B_rho(0)), letting r -> R and using mu(B_r(y)) <= mu(B_rho(0)) <= (1 + delta) omega_n rho^n, gives omega_n^-1 s_*^-n mu(B_{s_*}(y)) <= e^(2 Lambda)(1 + delta)(1 - kappa_0)^-n + 2 e^Lambda Lambda/omega_n <= e^(2 Lambda)(1 + delta)(1 + eps_1/2) + 2 e^Lambda Lambda/omega_n <= 1 + eps_1 for delta small.
 (b) If |y| > kappa_0 rho: let R := |y|/(1 - theta_0); then kappa_0 rho < R < rho (because gamma_b/(1 - theta_0) < 1). Let V~ be the dilation of V by 1/R (Inv), a contract varifold in U/R, which contains the closed ball B_{rho/R}(0), hence B_1(0), with generalized mean curvature H~; xi~ := y/R has |xi~| = 1 - theta_0. Hypotheses of the sibling 6.1 for V~ with lambda := delta, theta := theta_0, Lambda~ = 2 omega_n and the 6.1-parameter delta~ := 3 C_1 delta (< 1/4 for delta small): for every r in [delta, 1], |mu~(B_1(0))/omega_n - mu~(B_delta(0))/(omega_n delta^n)| = |omega_n^-1 R^-n mu(B_R(0)) - omega_n^-1 (delta R)^-n mu(B_{delta R}(0))| <= 2 C_1 delta by (1a), and r^(1-n) integral_{B_r(0)} |H~| dmu~ = (rR)^(1-n) integral_{B_{rR}(0)} |H| dmu <= C_1 delta by (1b); and mu~(B_1(0)) = R^-n mu(B_R(0)) <= (1 + C_1 delta) omega_n <= 2 omega_n. The first conclusion of 6.1 with rho~ := theta_0 and tau := 2 delta (in [2 lambda, 1]) reads
 mu~(B_{(1 - delta~^(1/4)) theta_0}(xi~)) <= (2 delta)^-n mu~(B_{2 delta theta_0}(2 delta xi~)) + C_9 delta~^(1/4) |log delta|.
 In terms of V, (2 delta)^-n mu~(B_{2 delta theta_0}(2 delta xi~)) = (2 delta R)^-n mu(B_{2 delta theta_0 R}(2 delta y)); the centre 2 delta y has |2 delta y| <= 2 delta rho, B_{rho/2}(2 delta y) is in B_rho(0), and (M.v) at 2 delta y with R = rho/2 (letting r -> rho/2, mu(B_r(2 delta y)) <= mu(B_{rho/2 + 2 delta rho}(0))) together with (1a) at radius rho/2 + 2 delta rho gives omega_n^-1 (2 delta theta_0 R)^-n mu(B_{2 delta theta_0 R}(2 delta y)) <= e^(2 Lambda)(1 + 4 delta)^n (1 + C_1 delta) + 2 e^Lambda Lambda/omega_n <= 1 + C_2 delta. Hence, with r_y := (1 - delta~^(1/4)) theta_0 R:
 omega_n^-1 r_y^-n mu(B_{r_y}(y)) <= (1 - delta~^(1/4))^-n [1 + C_2 delta + C_9 delta~^(1/4) |log delta|/(omega_n theta_0^n)] =: 1 + eps_gamma(delta), with eps_gamma(delta) -> 0 as delta -> 0.
 As delta~^(1/4) <= 1/2 for delta small, r_y >= theta_0 R/2 > s_*; B_{r_y}(y) is contained in B_R(0) (|y| + r_y <= (1 - theta_0) R + theta_0 R), so (M.v) at y with R = r_y (letting r -> r_y) gives omega_n^-1 s_*^-n mu(B_{s_*}(y)) <= e^(2 Lambda)(1 + eps_gamma(delta)) + 2 e^Lambda Lambda/omega_n <= 1 + eps_1 for delta small.

3. Local graphs. Require delta <= eps_1 <= delta_7. For y in spt V cap B_{gamma_b rho}(0), the translate V - y (Inv) satisfies AllardHypotheses at radius s_* with parameter eps_1: mass by step 2, K(y, s_*) <= delta <= eps_1 (B_{s_*}(y) in B_rho(0) as s_* < (1 - gamma_b) rho), theta >= 1, 0 in spt(V - y). The sibling 5.2 gives a linear isometry q_y and u_y : R^n -> R^l, C^1 on B^n_{r_*}(0), r_* := gamma_7 s_* = c_* rho (c_* := gamma_7 kappa_0 theta_0/2 <= theta_0/2), with u_y(0) = 0, Du_y(0) = 0,
 spt V cap B_{r_*}(y) = (y + q_y '' graphOver u_y (B^n_{r_*}(0))) cap B_{r_*}(y), and sup |Du_y| <= C_7 eps_1^a =: eps_2 (Hilbert-Schmidt, hence also operator norm).
 Since r_* <= theta_0 rho/2 < gamma_b rho - gamma_a rho, B_{r_*}(y) is contained in B_{gamma_b rho}(0) when |y| <= gamma_a rho.

4. Flatness at 0. Require delta <= delta_7. The sibling 5.2 for V at (0, rho) gives q_0, u_0 with spt V cap B_{gamma_7 rho}(0) = q_0 '' graphOver u_0 (B^n_{gamma_7 rho}(0)) cap B_{gamma_7 rho}(0), u_0(0) = 0, Du_0(0) = 0, rho^-1 sup|u_0| + sup|Du_0| <= C_7 delta^a. Put T_0 := q_0(R^n x {0}) (= rotatedPlane q_0). For x = q_0(graphPoint(x', u_0(x'))) in spt V cap B_{gamma_7 rho}(0): dist(x, T_0) = |u_0(x')| <= C_7 delta^a |x'| <= C_7 delta^a |x|. (4)

5. Cone condition. Let kappa_1 in (0, theta_0] (fixed in step 6). Claim: for delta small (depending on gamma, kappa_1), dist(y, T_0) <= kappa_1 |y| for every y in spt V cap B_{gamma_b rho}(0). If |y| <= gamma_7' rho this follows from (4) once C_7 delta^a <= kappa_1. If |y| > gamma_7' rho, let R, V~, xi~ be as in 2(b) (so gamma_7' rho < R < rho). The first conclusion of 6.1 with rho~ := kappa_1/8 (in (0, theta_0]) and tau := gamma_7' rho/(2R) (in [2 delta, 1] for delta <= gamma_7'/4) gives
 mu~(B_{(1 - delta~^(1/4)) kappa_1/8}(xi~)) <= tau^-n mu~(B_{tau kappa_1/8}(tau xi~)) + C_9 delta~^(1/4) |log delta|.
 The left side is >= mu~(B_{kappa_1/16}(xi~)) = R^-n mu(B_{R kappa_1/16}(y)) >= omega_n (kappa_1/16)^n/2 by (1d) (R kappa_1/16 <= (1 - gamma_b) rho/2). If C_9 delta~^(1/4) |log delta| < omega_n (kappa_1/16)^n/2 (true for delta small), then mu(B_{tau kappa_1 R/8}(tau y)) > 0, so there is z in spt mu with |z - tau y| <= tau kappa_1 R/8; then |z| <= tau R (1 - theta_0 + kappa_1/8) <= tau R = gamma_7' rho/2 < rho, so z in spt V cap B_{gamma_7 rho}(0) and dist(z, T_0) <= C_7 delta^a gamma_7' rho/2 by (4). As dist(., T_0) is positively homogeneous and 1-Lipschitz, dist(y, T_0) = tau^-1 dist(tau y, T_0) <= tau^-1 (dist(z, T_0) + |z - tau y|) <= C_7 delta^a R + kappa_1 R/8 <= (8/7)(C_7 delta^a + kappa_1/8)|y| <= kappa_1 |y| once C_7 delta^a <= kappa_1/2 (R = |y|/(1 - theta_0) <= (8/7)|y|).

6. One graph over T_0. Choose eps_1 in (0, min{1/4, delta_7, delta_6}] with eps_2 = C_7 eps_1^a <= 1/24 (this fixes kappa_0, s_*, r_*, c_*, depending on n, l, p, gamma), and kappa_1 := min{theta_0, c_*/48, 1 - gammahat/gamma_a}. Put vartheta := 2 kappa_1/c_* + eps_2 <= 1/12.
 (a) Local planes. For y in spt V cap B_{gamma_a rho}(0) let T_y := q_y(R^n x {0}). For a unit vector e = q_y(graphPoint(e', 0)) in T_y the points y_+- := y + q_y(graphPoint(+-(r_*/2) e', u_y(+-(r_*/2) e'))) lie in spt V cap B_{r_*}(y), a subset of spt V cap B_{gamma_b rho}(0), and y_+ - y_- = r_* e + q_y(graphPoint(0, w)) with |w| <= eps_2 r_*. By step 5, |Q_0 y_+-| <= kappa_1 |y_+-| <= kappa_1 rho, so r_* |Q_0 e| <= 2 kappa_1 rho + eps_2 r_*, i.e. |Q_0 e| <= vartheta for every unit e in T_y; hence |P_0 v| >= (1 - vartheta)|v| for v in T_y.
 (b) Local graphs over T_0. Let Psi_y(x') := y + q_y(graphPoint(x', u_y(x'))) and Phi_y := P_0 o Psi_y on B^n_{r_*}(0), and A_y : R^n -> T_0, A_y x' := P_0 q_y(graphPoint(x', 0)). By (a), |A_y x'| >= (1 - vartheta)|x'|, so A_y is a linear bijection onto the n-dimensional T_0 with ||A_y^-1|| <= (1 - vartheta)^-1 <= 12/11; Phi_y = P_0 y + A_y + g_y with g_y(x') := P_0 q_y(graphPoint(0, u_y(x'))) eps_2-Lipschitz and g_y(0) = 0. Hence (i) |Phi_y(x'_1) - Phi_y(x'_2)| >= (1 - vartheta - eps_2)|x'_1 - x'_2| >= (7/8)|x'_1 - x'_2|; (ii) for every w in D_y := T_0 cap B_{r_*/2}(P_0 y) the map x' -> A_y^-1 (w - P_0 y - g_y(x')) maps B^n_{0.6 r_*}(0) into itself (|A_y^-1 (w - P_0 y)| + (12/11) eps_2 0.6 r_* <= (12/11)(0.5 + 0.025) r_* < 0.6 r_*) and is a contraction (constant <= (12/11) eps_2 < 1), so it has a fixed point x'(w), i.e. Phi_y(x'(w)) = w, and Psi_y(x'(w)) is in spt V cap B_{r_*}(y) (|Psi_y(x'(w)) - y| <= (1 + eps_2) 0.6 r_* < r_*); (iii) every x in spt V cap B_{r_*}(y) with P_0 x in D_y equals Psi_y(x') for some x' with Phi_y(x') = P_0 x, so x = Psi_y(x'(P_0 x)) by (i). Thus spt V cap B_{r_*}(y) cap P_0^-1(D_y) = {w + v_y(w) : w in D_y} with v_y(w) := Q_0 Psi_y(x'(w)); by the inverse function theorem (D Phi_y = P_0 D Psi_y is invertible) v_y is C^1 on the interior of D_y, and since ||Q_0 D Psi_y|| <= vartheta + eps_2 <= 1/8 (|Q_0 e| <= vartheta for unit e in T_y, |Du_y| <= eps_2) and ||(D Phi_y)^-1|| <= (1 - vartheta - eps_2)^-1 <= 8/7, ||D v_y|| <= 1/7.
 (c) P_0 is injective on spt V cap B_{gamma_a rho}(0): if P_0 y_1 = P_0 y_2 then |y_1 - y_2| = |Q_0 y_1 - Q_0 y_2| <= 2 kappa_1 gamma_a rho <= c_* rho/24 < r_*, so y_1 = Psi_{y_1}(0) and y_2 are points of spt V cap B_{r_*}(y_1) over the same point of D_{y_1}, hence equal by (b)(iii).
 (d) So there is v : D -> T_0^perp, D := P_0(spt V cap B_{gamma_a rho}(0)), with spt V cap B_{gamma_a rho}(0) = {w + v(w) : w in D}; and v = v_y on D cap D_y for every y in spt V cap B_{gamma_a rho}(0) (if w = P_0 x in D_y with x in spt V cap B_{gamma_a rho}(0), then |x - y| <= |P_0 x - P_0 y| + |Q_0 x| + |Q_0 y| <= r_*/2 + 2 kappa_1 rho < r_*, so x is the point of (b)(iii)).
 (e) D contains Omega := T_0 cap B^o_{gammahat rho}(0). Let D' := D cap Omega. 0 in D' (0 in spt V). D' is open in Omega: for w = P_0 y in D' and w' in D_y cap Omega, the point x' := w' + v_y(w') is in spt V cap B_{r_*}(y), a subset of spt V cap B_{gamma_b rho}(0), so by step 5 |x'| <= |w'| + kappa_1 |x'|, i.e. |x'| <= |w'|/(1 - kappa_1) < gammahat rho/(1 - kappa_1) <= gamma_a rho; hence w' = P_0 x' in D', and D_y cap Omega is a neighbourhood of w in Omega. D' is closed in Omega: if w_k = P_0 y_k in D' converge to w in Omega, then |y_k| <= |w_k|/(1 - kappa_1) <= gamma_a rho; a subsequence converges to some y with |y| <= gamma_a rho < rho, y in spt mu (closed) and in U, so y in spt V cap B_{gamma_a rho}(0) and P_0 y = w. Omega is connected, so D' = Omega.
 (f) Define u : B^o_{gammahat rho}(0) -> R^l by q_0(graphPoint(x', u(x'))) := q_0(graphPoint(x', 0)) + v(q_0(graphPoint(x', 0))) (using T_0 = q_0(R^n x {0}), T_0^perp = q_0({0} x R^l)). By (d), u is C^1 with ||Du|| <= 1/7. For |x'| <= gamma_7' rho/2 the point q_0(graphPoint(x', u_0(x'))) has norm < gamma_7' rho, so it lies in spt V cap B_{gamma_a rho}(0) over q_0(graphPoint(x', 0)); by (c), u = u_0 on B^n_{gamma_7' rho/2}(0), hence u(0) = 0, Du(0) = 0. Finally spt V cap B_{gamma rho}(0) = q_0 '' graphOver u (B^n_{gamma rho}(0)) cap B_{gamma rho}(0): each x in spt V cap B_{gamma rho}(0) is w + v(w) with w = P_0 x, |w| <= |x| <= gamma rho; conversely for |x'| <= gamma rho < gammahat rho, w := q_0(graphPoint(x', 0)) is in D and w + v(w) is in spt V.

7. Rate.
 (a) On the graph. Every point w + v(w), w in Omega, lies in spt V cap B_{gamma_a rho}(0), a subset of B^o_rho(0). By (M.iv), (UD) and (F2), on B^o_{gamma_a rho}(0) we have mu = theta H^n restricted to spt V with theta >= 1 H^n-a.e., and by (F1), for H^n-a.e. x = q_0(graphPoint(x', u(x'))), T_xM = q_0(graph Du(x')).
 (b) Height. For x' in B^o_{gammahat rho}(0) and x := q_0(graphPoint(x', u(x'))): u(0) = 0 and ||Du|| <= 1/7 give |x| <= 2|x'|; for H^n-a.e. such x, T_xM = q_0(graph Du(x')) contains q_0(graphPoint(x', Du(x') x')) and x - q_0(graphPoint(x', Du(x') x')) = q_0(graphPoint(0, u(x') - Du(x') x')), so by (Nor) |p_x^perp x| >= |u(x') - Du(x') x'|/2. With (1c), (a) and (Area) (J >= 1): integral_{B^n_{gammahat rho}} |u(x') - Du(x') x'|^2 |x'|^(-n-2) dx' <= 4 * 2^(n+2) integral_{B^o_rho(0)} |p_x^perp x|^2 |x|^(-n-2) dmu <= 2^(n+4) C_1 delta. In polar coordinates x' = r w (w in S^(n-1) with the measure H^(n-1); for n = 1, S^0 = {-1, 1} with counting measure), W(r,w) := u(rw)/r satisfies d/dr W(r,w) = (Du(rw) rw - u(rw))/r^2, hence integral_S integral_0^(gammahat rho) r |d/dr W|^2 dr dw = integral_{B^n_{gammahat rho}} |u - Du x'|^2 |x'|^(-n-2) dx' <= 2^(n+4) C_1 delta. Let r_1 := gamma_7' rho/2; for r <= r_1, |W(r,w)| = |u_0(rw)|/r <= sup |Du_0| <= C_7 delta^a (u = u_0 there, u_0(0) = 0). For r_1 <= r < gammahat rho, D_r := W(r,.) - W(r_1,.) satisfies |D_r(w)|^2 <= log(r/r_1) integral_{r_1}^r t |d/dt W(t,w)|^2 dt (Cauchy-Schwarz), so integral_S |D_r|^2 <= log(2 gammahat/gamma_7') 2^(n+4) C_1 delta =: m_0. D_r is 1-Lipschitz on S^(n-1) (|W(t,w) - W(t,w')| <= ||Du|| |w - w'|, and ||Du_0|| <= 1 for delta small) and |D_r| <= 1. If n >= 2 and |D_r(w_0)| = m, then |D_r| >= m/2 on S^(n-1) cap B_{m/2}(w_0), whose H^(n-1)-measure is >= c_n m^(n-1), so c_n m^(n+1)/4 <= m_0; for n = 1, m^2 <= m_0. Hence sup |D_r| <= C m_0^(1/(n+1)) <= C_gamma delta^(1/(n+1)), and
 |u(x')| <= C_gamma delta^a |x'| for x' in B^o_{gammahat rho}(0). (H)
 (c) Tilt. Let gamma' := (gamma + gammahat)/2, r_gamma := (gammahat - gamma') rho/4, and zeta = q_0(graphPoint(z, u(z))) with |z| <= gamma' rho. Points x of spt V cap B_{r_gamma}(zeta) have |x| <= |zeta| + r_gamma < gammahat rho (for delta small, |zeta| <= (1 + C_gamma delta^a) gamma' rho by (H)), so x = w + v(w) with |w| <= |x| < gammahat rho, i.e. x = q_0(graphPoint(x', u(x'))) with |x'| < gammahat rho, and dist(x - zeta, T_0) <= |u(x')| + |u(z)| <= 2 C_gamma delta^a rho =: h. Lemma A (B_{r_gamma}(zeta) in U), (1d) (mu(B_{r_gamma}(zeta)) <= C_1' omega_n r_gamma^n, as r_gamma <= (1 - gamma_b) rho/2) and Hoelder (integral_{B_{r_gamma}(zeta)} |H| <= delta rho^(n/p - 1) (C_1' omega_n r_gamma^n)^(1 - 1/p) <= C_gamma delta r_gamma^(n-1)) give E(zeta, r_gamma/2, T_0) <= (r_gamma/2)^-n [144 r_gamma^-2 h^2 C_1' omega_n r_gamma^n + 4 h C_gamma delta r_gamma^(n-1)] <= C_gamma delta^(2a) (h/r_gamma <= C_gamma delta^a, delta <= delta^a).
 (d) Decay. For zeta as in (c), zeta is in spt V cap B_{gamma_b rho}(0), so by step 2 the translate V - zeta satisfies 2.3 at (0, s_*) with parameter eps_1 <= delta_6, and by (1d) the density bounds of (Iter) hold with c_l = 1/2, c_u = C_1' for radii <= (1 - gamma_b) rho/2. Let sigma_gamma := min{r_gamma/2, eps_1 s_*/2} (a fixed multiple of rho) and E_2 := E_*(zeta, sigma_gamma, T_0) (parameter eps_1) <= max{(r_gamma/(2 sigma_gamma))^n E(zeta, r_gamma/2, T_0), eps_1^-1 delta^2} <= C_gamma delta^(2a) (K(zeta, sigma_gamma) <= delta and delta^2/eps_1 <= delta <= delta^(2a)). (Iter) gives the limit plane S(zeta) with |p_{S(zeta)} - P_0|^2 <= C_II E_2 and E(zeta, s, S(zeta)) <= C_III (s/sigma_gamma)^(2 alpha') E_2 for 0 < s <= sigma_gamma.
 (e) C^(1,alpha') estimate. For mu-a.e. such zeta = q_0(graphPoint(z, u(z))): p_zeta = p_{S(zeta)}, because by (Leb) zeta is a Lebesgue point of x -> p_x and |p_zeta - p_{S(zeta)}|^2 <= 2 mu(B_s(zeta))^-1 integral_{B_s(zeta)} |p_x - p_zeta|^2 dmu + (4/omega_n) E(zeta, s, S(zeta)) -> 0 as s -> 0 (mu(B_s(zeta)) >= omega_n s^n/2 by (1d)); and p_zeta = p_{q_0(graph Du(z))} by (a). By (a) and (Area), mu-null subsets of the graph correspond to L^n-null sets of parameters, so both identities hold for L^n-a.e. z in B^n_{gamma' rho}(0). By (Ang) and ||Du|| <= 1/7: ||Du(z)|| <= 2 ||p_{q_0(graph Du(z))} - P_0|| = 2 ||p_{S(zeta)} - P_0|| <= 2 (C_II E_2)^(1/2) <= C_gamma delta^a for a.e., hence (by continuity) every, z in B^n_{gamma' rho}(0); so |Du| <= sqrt(n) C_gamma delta^a <= L_0 (Hilbert-Schmidt) on B^n_{gamma' rho}(0) for delta small, and (Gp) applies to any two values of Du on B^n_{gamma' rho}(0). Let s_gamma := min{sigma_gamma, (gamma' - gamma) rho} (a fixed multiple of rho). Campanato: for a.e. z in B^n_{gamma rho}(0) and 0 < s <= s_gamma, the ball B^n_{s/2}(z) lies in B^n_{gamma' rho}(0) and the graph points over it lie in B_s(zeta) (||Du|| <= 1/7), so by (Gp), (Area) (J >= 1) and (a), integral_{B^n_{s/2}(z)} |Du(x') - Du(z)|^2 dx' <= integral_{B^n_{s/2}(z)} |p_{q_0(graph Du(x'))} - p_{S(zeta)}|^2 dx' <= integral_{B_s(zeta)} |p_x - p_{S(zeta)}|^2 dmu = s^n E(zeta, s, S(zeta)) <= C_III s^n (s/sigma_gamma)^(2 alpha') E_2. For x_1, x_2 in B^n_{gamma rho}(0) with d := |x_1 - x_2| <= s_gamma/2 and midpoint m, B^n_{d/2}(m) is contained in B^n_d(x_1) cap B^n_d(x_2); averaging |Du(x_1) - Du(x_2)|^2 <= 2|Du(x) - Du(x_1)|^2 + 2|Du(x) - Du(x_2)|^2 over x in B^n_{d/2}(m) and using the previous inequality with s = 2d (for a.e. x_1, x_2, then for all by continuity) gives |Du(x_1) - Du(x_2)|^2 <= (2^(2n+2) C_III/omega_n)(2d/sigma_gamma)^(2 alpha') E_2, i.e. |Du(x_1) - Du(x_2)| <= C_gamma (d/rho)^alpha' delta^a; for d > s_gamma/2, |Du(x_1) - Du(x_2)| <= 2 sup_{B^n_{gamma rho}} |Du| <= C_gamma (2 d/s_gamma)^alpha' delta^a.

8. Conclusion. With q := q_0 and u from 6(f): u is C^1 on the open ball B^o_{gammahat rho}(0), which contains the closed ball B^n_{gamma rho}(0), so u is ContDiffOn 1 there and fderivWithin = Du; u(0) = 0, Du(0) = 0; the support identity is 6(f); and on B^n_{gamma rho}(0), rho^-1 sup|u| <= C_gamma delta^a by (H), sup|Du| <= sqrt(n) C_gamma delta^a and rho^alpha' sup_{x != y} |Du(x) - Du(y)|/|x - y|^alpha' <= C_gamma delta^a by 7(e). All suprema are finite, so scaledC1AlphaNorm u (B^n_{gamma rho}(0)) (1 - n/p) rho <= ofReal(C_gamma delta^(1/(2n+2))), i.e. AllardConclusion V p delta rho gamma C_gamma holds. delta_0(gamma) in (0,1) is the minimum of the thresholds used: delta <= kappa, delta < 1/4, delta <= eps_1 and delta <= delta_7, delta~ = 3 C_1 delta < 1/4 and delta~^(1/4) <= 1/2, the lower bound in (1d), the smallness conditions in steps 2, 5, 7(c), 7(e), and 2 delta <= gamma_7'/2; C_gamma depends only on n, l, p, gamma.

## Key steps

1. Mass-ratio, curvature and conical-excess pinching at centre 0 (corrected monotonicity, (M.v))
2. 6.1 after dilation, plus (M.v), gives pinching at every y in spt V cap B_{gamma_b rho}(0)
3. 5.2 at each such y gives local graphs at a fixed scale c_* rho
4. 6.1 again, with 5.2 at 0, gives the thin-cone condition around T_0
5. Local planes are close to T_0; contraction mapping, injectivity of P_0 and connectedness give one graph over T_0
6. Rate: conical excess at 0 and radial integration, then Lemma A, the 4.5 iteration and Campanato on B^n_{gamma' rho}

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

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/5942

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
