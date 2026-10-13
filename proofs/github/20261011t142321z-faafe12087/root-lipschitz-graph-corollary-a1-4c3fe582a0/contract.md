<!-- theorem-id: gmt-ch05/root.lipschitz_graph_corollary-a1 -->

## Theorem `Submission.lipschitz_graph_corollary`

For n >= 1, l, p > n there is beta in (0,1/4] (depending on n,l,p) such that for all L in (0,1], K >= 0, open U, V with generalized mean curvature H, delta, rho with 0 < delta <= (beta L)^(2n+2) and AllardHypotheses H p delta rho, every linear isometry q with dist(x, T_0) <= K delta^(1/(2n+2)) delta rho on spt V cap B_{2 delta rho}(0) (T_0 := q(R^n x {0})) and with E(xi, sigma, T_0) <= beta^2 L^2 for all xi in spt V cap B_{delta rho/2}(0), sigma in (0, delta rho/2], there is f: R^n -> R^l, L-Lipschitz on B^n_{delta rho/4}(0), with |f| <= K delta^(1/(2n+2)) delta rho there and spt V cap B_{delta rho/4}(0) = q(graph f over B^n_{delta rho/4}(0)) cap B_{delta rho/4}(0).

Node: `root.lipschitz_graph_corollary-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/113

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/716, https://github.com/ZhengyangZhang06/gmt-formalize/issues/717, https://github.com/ZhengyangZhang06/gmt-formalize/issues/719, https://github.com/ZhengyangZhang06/gmt-formalize/issues/724, https://github.com/ZhengyangZhang06/gmt-formalize/issues/727

## Lean problem

Declaration: `Submission.lipschitz_graph_corollary`

```lean
LipschitzGraphCorollary
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
- Child DAG node: `root.lipschitz_graph_corollary-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 5, Corollary 2.7 and its printed proof (p. 113), which re-uses the set G, the Lipschitz construction and inequality (10) from the proof of Lemma 2.6; those parts are reproduced here (the corollary has its own constant beta). Contract normalization as in 2.6: arbitrary linear isometry q, T_0 = q(R^n x {0}), height constant K >= 0, sup bound K delta^alpha sigma_0. Corrections as in 2.6: monotonicity with the correct constant Lambda = 4 p delta/(p-n) (Ch. 4, 4.2, kappa = (p-n)/(4p)); the annulus in (10) is B_{3s} minus B_s; the extension loss sqrt(l) is absorbed into beta; the sup bound comes from a retraction; graph points far from spt V are reached by a continuity (path) argument.

Notation (contract). mu := V.weight = theta H^n restricted to M (M = V.carrier, theta = V.mult); spt V := V.support = U cap spt mu; p_x := V.tangentProj x and p_x^perp := I - p_x; |A| is the Hilbert-Schmidt norm (hsNorm), ||A|| the operator norm, ||A|| <= |A| <= sqrt(rank A) ||A||; B_s(y) is the closed ball and B^o_s(y) the open ball; omega_n := unitBallVolume n; K(z,s) := (s^(p-n) integral_{B_s(z)} |H|^p dmu)^(1/p) in [0,infinity] (the contract's scaledLpNorm); E(z,s,T) := s^-n integral_{B_s(z)} |p_x - p_T|^2 dmu (tiltExcess); kappa := (p-n)/(4p) > 0; a := 1/(2n+2). Under 2.3, if B_s(z) is contained in B_rho(0) then K(z,s)^p = s^(p-n) integral_{B_s(z)} |H|^p <= (s/rho)^(p-n) rho^(p-n) integral_{B_rho(0)} |H|^p, so K(z,s) <= (s/rho)^(1-n/p) delta <= delta.
Further notation: sigma_0 := delta rho; alpha := a = 1/(2n+2); T_0 := rotatedPlane q; P := p_{T_0}; Q := I - P; tilt(A) := integral_A |p_x - P|^2 dmu; q^-1 y = graphPoint(a(y), b(y)), so |a(y)| = |Py| <= |y| and |b(y)| = |Qy| = dist(y, T_0); G' := spt V cap B_{sigma_0/2}(0). The tilt hypothesis reads: tilt(B_s(xi)) <= beta^2 L^2 s^n for all xi in G' and s in (0, sigma_0/2].

Sibling used: AffineApproximationLemma, with constant C_A >= 1 (enlarging the constant preserves both inequalities): for 0 < delta <= 1/4, 2.3, xi in spt V cap B_{delta rho}(0), s in (0, 2 delta rho] there is an n-plane T' with C_A^-1 (s^-n integral_{B_{s/2}(xi)} |p_x - p_{T'}|^2)^(1/2) <= s^-1 h(xi,s,T') + K(xi,s) and s^-1 h(xi,s,T') <= C_A delta^alpha, h(xi,s,T') := sup{dist(x - xi, T') : x in spt V cap B_s(xi)}.

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
(Ext) [Ch. 2, 1.2 (McShane), componentwise] An M-Lipschitz map from a subset of R^n to R^l extends to an (sqrt(l) M)-Lipschitz map on R^n.

Proof. Constants C_1, C_2, ... depend only on n, l, p and not on beta, L, K, delta, rho, q; beta in (0,1/4] is fixed in step 7. Let L in (0,1], K >= 0, 0 < delta <= (beta L)^(2n+2), 2.3, q with the height hypothesis, and the tilt hypothesis. Then delta <= beta^(2n+2) <= delta_P <= 1/8 (step 7), delta^alpha <= beta L, and every centre used below lies in B_{sigma_0}(0) (a subset of B_{3 delta rho}(0)) with radii <= sigma_0 <= rho/2, so (P) is available.

1. Height (book: T(2 sigma_0, 0) is close to T_0). The sibling at (0, sigma_0) gives an n-plane T* with h(0, sigma_0, T*) <= C_A delta^alpha sigma_0 and (K(0, sigma_0) <= delta <= delta^alpha) integral_{B_{sigma_0/2}(0)} |p_x - p_{T*}|^2 <= C_A^2 (C_A + 1)^2 delta^(2 alpha) sigma_0^n <= C_A^2 (C_A + 1)^2 beta^2 L^2 sigma_0^n. The tilt hypothesis at (0, sigma_0/2) (0 in G') gives tilt(B_{sigma_0/2}(0)) <= beta^2 L^2 (sigma_0/2)^n. Integrating |P - p_{T*}|^2 <= 2|p_x - P|^2 + 2|p_x - p_{T*}|^2 over B_{sigma_0/2}(0) (measure >= omega_n (sigma_0/2)^n/2 by (P.ii)): |P - p_{T*}| <= C_2 beta L, C_2 := (4 (1 + 2^n C_A^2 (C_A+1)^2)/omega_n)^(1/2). Hence for x in spt V cap B_{sigma_0}(0): dist(x, T_0) <= dist(x, T*) + ||p_{T*} - P|| |x| <= (C_A + C_2) beta L sigma_0 =: h_0, i.e. h_0 = C_3 beta L sigma_0 with C_3 := C_A + C_2.

2. Lipschitz property on G' (book: 'the set G ... includes all of spt mu cap B_{sigma_0/2}(0)'). Let y_1 != y_2 in G' and s := |y_1 - y_2| <= sigma_0.
 (a) If s <= sigma_0/2: the tilt hypothesis at (y_1, s/2) gives tilt(B_{s/2}(y_1)) <= beta^2 L^2 (s/2)^n <= beta^2 L^2 s^n; the sibling at (y_1, s) (y_1 in spt V cap B_{delta rho}(0), s <= 2 delta rho) gives T_1 with h(y_1, s, T_1) <= C_A delta^alpha s and integral_{B_{s/2}(y_1)} |p_x - p_{T_1}|^2 <= C_A^2 (C_A + 1)^2 delta^(2 alpha) s^n; comparing on B_{s/2}(y_1) (measure >= omega_n (s/2)^n/2): |P - p_{T_1}| <= C_5 beta L, C_5 := (2^(n+2) (1 + C_A^2 (C_A+1)^2)/omega_n)^(1/2); hence |Q(y_2 - y_1)| <= dist(y_2 - y_1, T_1) + ||P - p_{T_1}|| s <= (C_A + C_5) beta L s =: C_6 beta L s.
 (b) If s > sigma_0/2: |Q(y_2 - y_1)| <= |Q y_1| + |Q y_2| <= 2 h_0 < 4 C_3 beta L s.
 With eps_1 := max{C_6, 4 C_3} beta and eps_1 L <= 1/2: |Q(y_2 - y_1)| <= eps_1 L (|P(y_2 - y_1)| + |Q(y_2 - y_1)|), so |b(y_2) - b(y_1)| <= 2 eps_1 L |a(y_2) - a(y_1)|. Hence a is injective on G' and g : a(G') -> R^l, g(a(y)) := b(y), is (2 eps_1 L)-Lipschitz.

3. Extension and sup bound. By (Ext) there is f_1 : R^n -> R^l with f_1 = g on a(G') and Lip f_1 <= 2 sqrt(l) eps_1 L =: eps_0 L. Let R_0 := min{K delta^alpha sigma_0, h_0}, pi the nearest-point retraction of R^l onto the closed ball of radius R_0 about 0, and f := pi o f_1. Points y of G' lie in spt V cap B_{2 sigma_0}(0) and in spt V cap B_{sigma_0}(0), so |b(y)| <= K delta^alpha sigma_0 (height hypothesis) and |b(y)| <= h_0 (step 1); hence f = g on a(G'). Thus Lip f <= eps_0 L <= L on R^n (eps_0 <= 1), so f is L-Lipschitz on B^n_{sigma_0/4}(0), and |f| <= K delta^alpha sigma_0 everywhere. Fhat := {q(graphPoint(x, f(x))) : x in R^n} (closed, as f is continuous) contains G', and |Q(x - z)| <= eps_0 |x - z| for x, z in Fhat.

4. Inclusion spt V cap B_{sigma_0/4}(0) subset q '' graphOver f (B^n_{sigma_0/4}(0)) cap B_{sigma_0/4}(0): if y is in the left side, then y in G', |a(y)| <= |y| <= sigma_0/4 and y = q(graphPoint(a(y), f(a(y)))).

5. Claim (10') [book (9),(10) with the annulus B_{3s} minus B_s]. Let zeta in Fhat minus spt V with |zeta| <= sigma_0/4 + sigma_0/64 and 0 < d := dist(zeta, spt V) <= sigma_0/64, s := d/2. Then s^n <= C_8 [mu(B_{3s}(zeta) minus Fhat) + tilt(B_{3s}(zeta))].
 Proof. (a) Since spt mu is closed and |zeta| + d < rho, there is y in spt mu with |y - zeta| = dist(zeta, spt mu) <= d; then |y| < rho, so y in U, y in spt V, |y - zeta| = d, and |y| <= 9 sigma_0/32. The open ball B^o_d(zeta) misses spt mu, so mu(B_s(zeta)) = 0 (F2). (b) (M) at zeta with R := (1 - 3 delta) rho and Lambda = delta/kappa <= 1: as Phi(s) = F(s) - 1, (M.ii) with r = 3s gives F(3s)(3s)^-n mu(B_{3s}(zeta)) <= 2 Lambda + e^Lambda s^(-n-2) I, I := integral_{B_{3s}(zeta)} |p_x^perp(x - zeta)|^2 dmu (since |x - zeta| >= s on the annulus); with F(3s) >= e^-Lambda, (3s)^-n mu(B_{3s}(zeta)) <= 2 e Lambda + e^2 s^(-n-2) I. (c) B_s(y) is contained in B_{3s}(zeta) and mu(B_s(y)) >= omega_n s^n/2 by (P.ii), so (3s)^-n mu(B_{3s}(zeta)) >= 3^-n omega_n/2; as delta <= delta_8 (step 7), 2 e Lambda <= 3^-n omega_n/4, hence s^(n+2) <= 4 * 3^n e^2 omega_n^-1 I. (d) On B_{3s}(zeta), p_x^perp = Q + (P - p_x), so |p_x^perp(x - zeta)|^2 <= 2|Q(x - zeta)|^2 + 18 s^2 |p_x - P|^2, with |Q(x - zeta)| <= 3 eps_0 s for x in Fhat and <= 3s otherwise; and mu(B_{3s}(zeta)) <= mu(B_{5s}(y)) <= 2 omega_n 5^n s^n by (P.i). So I <= 18 s^2 [2 omega_n 5^n eps_0^2 s^n + mu(B_{3s}(zeta) minus Fhat) + tilt(B_{3s}(zeta))]. (e) Hence s^n <= A_8 [2 omega_n 5^n eps_0^2 s^n + mu(B_{3s}(zeta) minus Fhat) + tilt(B_{3s}(zeta))], A_8 := 72 * 3^n e^2/omega_n; since eps_0^2 <= 1/(4 A_8 omega_n 5^n) the first term is <= s^n/2, giving the claim with C_8 := 2 A_8.

6. Reverse inclusion (book: '(10) gives sigma^n <= C beta^2 sigma^n, impossible'). Suppose zeta = q(graphPoint(x_z, f(x_z))) with |x_z| <= sigma_0/4 and |zeta| <= sigma_0/4, but zeta not in spt V. Since zeta in U, dist(zeta, spt V) > 0 (F2). Let gamma(t) := q(graphPoint(t x_z, f(t x_z))), t in [0,1]; |gamma(t)| <= sigma_0/4 + h_0 <= sigma_0/4 + sigma_0/64. The continuous function t -> dist(gamma(t), spt V) is <= |f(0)| <= h_0 <= sigma_0/64 at t = 0 (0 in spt V) and positive at t = 1. If its value at t = 1 is <= sigma_0/64 put zeta' := zeta; otherwise the intermediate value theorem gives t with dist(gamma(t), spt V) = sigma_0/64 and we put zeta' := gamma(t). In both cases zeta' in Fhat minus spt V satisfies the hypotheses of (10'), with 0 < d := dist(zeta', spt V) <= sigma_0/64; let s := d/2 <= sigma_0/128 and y as in (10')(a). Then B_{3s}(zeta') is contained in B_{sigma_0/4 + sigma_0/64 + 3 sigma_0/128}(0), a subset of B^o_{sigma_0/2}(0), so spt V cap B_{3s}(zeta') is contained in G', hence in Fhat, and mu(B_{3s}(zeta') minus Fhat) = 0 (F2). Thus (10') gives s^n <= C_8 tilt(B_{3s}(zeta')). But B_{3s}(zeta') is contained in B_{5s}(y), y in G' (|y| <= 9 sigma_0/32) and 5s <= sigma_0/2, so the tilt hypothesis gives tilt(B_{5s}(y)) <= beta^2 L^2 (5s)^n <= 5^n beta^2 s^n. Hence s^n <= C_8 5^n beta^2 s^n, impossible because C_8 5^n beta^2 < 1 (step 7). Therefore q '' graphOver f (B^n_{sigma_0/4}(0)) cap B_{sigma_0/4}(0) is contained in spt V, and with step 4, spt V cap B_{sigma_0/4}(0) = q '' graphOver f (B^n_{sigma_0/4}(0)) cap B_{sigma_0/4}(0).

7. Choice of beta in (0,1/4], depending only on n, l, p: beta^(2n+2) <= min{delta_P, delta_8} with delta_8 := 3^-n omega_n (p-n)/(32 e p); eps_1 = max{C_6, 4 C_3} beta <= 1/2; eps_0 = 2 sqrt(l) eps_1 <= 1 and eps_0^2 <= 1/(4 A_8 omega_n 5^n); C_3 beta <= 1/64 (so h_0 <= sigma_0/64); C_8 5^n beta^2 < 1. With this beta, steps 3, 4 and 6 give f with LipschitzOnWith L on B^n_{sigma_0/4}(0), |f| <= K delta^alpha sigma_0 there, and the support identity.

## Key steps

1. The tilt hypothesis makes T_0 close to T(0, sigma_0): height <= C beta L sigma_0
2. spt V cap B_{sigma_0/2}(0) is a small-Lipschitz graph over T_0
3. Extension plus retraction gives f with Lip <= L and the sup bound
4. Inclusion of spt V cap B_{sigma_0/4}(0) in the graph
5. (10') with the corrected monotonicity constants at a graph point near spt V, reached by a path
6. Reverse inclusion: (10') contradicts the tilt hypothesis

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

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/4360

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
