<!-- theorem-id: gmt-ch05/root.density_one_higher_regularity-a1.c1_graph_density-a1.graph_mass_pinching-a1 -->

## Theorem `Submission.dohr_c1_graph_mass_pinching`

Let n >= 1 and l be natural numbers, R ∈ R, u : R^n → R^l of class C^1 on the open ball B°_R(0) of R^n, x ∈ B°_R(0), and 0 < ε < 1. Let Γ = graphOver u (B°_R(0)) = {(z, u(z)) : z ∈ B°_R(0)} ⊆ R^{n+l} and let B_r((x, u(x))) denote the closed ball (with (x, u(x)) = graphPoint x (u x)). Then there is η > 0 such that for every r with 0 < r <= η, in [0, ∞]: ENNReal.ofReal(((1-ε)^n/(1+ε)^n) omega_n r^n) <= H^n(Γ ∩ B_r((x, u(x)))) <= ENNReal.ofReal(((1+ε)^n/(1-ε)^n) omega_n r^n), where H^n = μHE[n] and omega_n = unitBallVolume n.

Node: `root.density_one_higher_regularity-a1.c1_graph_density-a1.graph_mass_pinching-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/476

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/901, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1904

Decomposition children: None

## Lean problem

Declaration: `Submission.dohr_c1_graph_mass_pinching`

```lean
∀ n ℓ : ℕ, 1 ≤ n → ∀ (R : ℝ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 R) → ∀ x ∈ ball (0 : Rn n) R, ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, 0 < r → r ≤ η → ENNReal.ofReal ((1 - ε) ^ n / (1 + ε) ^ n * (unitBallVolume n * r ^ n)) ≤ (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) ∧ (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) ≤ ENNReal.ofReal ((1 + ε) ^ n / (1 - ε) ^ n * (unitBallVolume n * r ^ n))
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

- Parent DAG node: `root.density_one_higher_regularity-a1.c1_graph_density-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.c1_graph_density-a1.graph_mass_pinching-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 1-6 of the parent proof and the two-sided bound of its step 7: graph geometry, ε-control of Du near x0, localization, the ellipsoid sandwich, plane balls, comparison with the tangent plane, and the pinching bounds.

Deviation in step 6, forced by the frozen imports; the statement is unchanged. The parent proof computes H^n(G(D_r)) with simongmt's Chapter02.injective_area_formula_lipschitzOn and the Jacobian normDet. Neither is reachable from the frozen imports of GMT.Ch05.Submission: Lean reports an unknown identifier for Poincare.SimonGMT.Chapter02.injective_area_formula_lipschitzOn and an unknown constant for LinearMap.normDet, and a node implementation must preserve the frozen imports. Instead, G(D_r) is compared with balls of the tangent plane by the Lipschitz-image inequality for H^n (Mathlib LipschitzOnWith.hausdorffMeasure_image_le), applied to two mutually inverse maps. Accordingly, the following parts of the parent proof are dropped: the Jacobian bound |J(Du(x)) - J0| <= eps J0 of step 2, the normDet half of (A2) and the identity L^n(E_t) = omega_n t^n / J0 of step 5, and the area-formula integral of step 6. Kept are steps 1, 3 and 4, the Du-control of step 2, and from step 5 only H^n(L(R^n) ∩ B_t(0)) = omega_n t^n. This uses only the plane-ball half of fact (A2), which is the sibling rsod_planeMeasure_closedBall, and the ε-control of step 2, which is the sibling dohr_c1_uniform_first_order. The ellipsoids E_t of the parent proof are used translated by -x0, so only balls centred at 0 in the linear plane range L occur. The pinching ratios become ((1-ε)/(1+ε))^n and ((1+ε)/(1-ε))^n instead of (1-ε)(1+ε)^{-n} and (1+ε)(1-ε)^{-n}. Both still tend to 1 as ε → 0.

Notation. For x ∈ R^n and y ∈ R^l, (x, y) := graphPoint x y ∈ R^{n+l}: the first n coordinates are x and the last l are y. G(z) := (z, u(z)). x0 denotes the given point x ∈ B°_R(0). P := Du(x0) = fderiv R u x0 and y0 := G(x0) = graphPoint x0 (u x0). Γ := G(B°_R(0)) = graphOver u (ball 0 R). H^n := μHE[n], omega_n := unitBallVolume n, ofReal := ENNReal.ofReal. B_ρ(z) is a closed ball and B°_ρ(z) an open ball. All measure inequalities are in [0, ∞]. Hypotheses: n ≥ 1, u C^1 on B°_R(0), x0 ∈ B°_R(0), 0 < ε < 1.

1. Graph coordinates. The k-th coordinate of (x, y) is x_k for k < n and y_{k-n} for n ≤ k < n+l (Fin.addCases, Fin.append_left, Fin.append_right). Hence (x + x', y + y') = (x, y) + (x', y'), (cx, cy) = c(x, y) and (x - x', y - y') = (x, y) - (x', y'). Splitting the sum of squared coordinates (EuclideanSpace.norm_sq_eq, Fin.sum_univ_add) gives |(x, y)|^2 = |x|^2 + |y|^2. So |x| ≤ |(x, y)| and |(0, y)| = |y|. The first-coordinates map π(w) := (w_1, ..., w_n) ∈ R^n, w ∈ R^{n+l}, satisfies π((x, y)) = x.

2. Tangent map. By step 1 and the linearity of P, L v := (v, P v) defines a linear map L : R^n → R^{n+l}. Step 1 gives |v| ≤ |L v|, so L is injective, and π(L v) = v. Also G(x) - G(x') = (x - x', u(x) - u(x')). Therefore |x - x'| ≤ |G(x) - G(x')|, and π(G(x)) = x.

3. First-order estimate. Apply dohr_c1_uniform_first_order to the open set U = B°_R(0), the map u, the point x0 and ε > 0. This gives η0 > 0 such that B := B_{η0}(x0) ⊆ B°_R(0) and |u(x) - u(x') - P(x - x')| ≤ ε|x - x'| for all x, x' ∈ B. For x, x' ∈ B, step 1 gives G(x) - G(x') - L(x - x') = (0, u(x) - u(x') - P(x - x')). Hence
 |G(x) - G(x') - L(x - x')| = |u(x) - u(x') - P(x - x')| ≤ ε|x - x'| ≤ ε|L(x - x')|.
 By the triangle inequality, for all x, x' ∈ B:
 (3a) |G(x) - G(x')| ≤ (1 + ε)|L(x - x')|;
 (3b) (1 - ε)|L(x - x')| ≤ |G(x) - G(x')|.

4. Choice of η. Put η := (1 - ε)η0 > 0, which is positive because 0 < ε < 1. Fix r with 0 < r ≤ η. Then r ≤ η0, r/(1 - ε) ≤ η0, and r/(1 + ε) ≤ r ≤ η0.

5. Localization. Let D := {x ∈ B°_R(0) : |G(x) - y0| ≤ r} = B°_R(0) ∩ G^{-1}(B_r(y0)). Unfolding graphOver and using f(s) ∩ t = f(s ∩ f^{-1}(t)) (Set.image_inter_preimage) gives Γ ∩ B_r(y0) = G(D). For x ∈ D, step 2 gives |x - x0| ≤ |G(x) - G(x0)| ≤ r ≤ η0, so D ⊆ B.

6. Centred ellipsoid sandwich. For t ∈ R let E_t := {v ∈ R^n : |L v| ≤ t}. If t ≤ η0 and v ∈ E_t, then x0 + v ∈ B, because |(x0 + v) - x0| = |v| ≤ |L v| ≤ t ≤ η0.
 (6a) If v ∈ E_{r/(1+ε)}, then x0 + v ∈ D. Indeed x0 + v ∈ B by the first sentence of this step, with t = r/(1 + ε) ≤ η0 (step 4), and B ⊆ B°_R(0) by step 3. By (3a) with x = x0 + v and x' = x0 (both in B): |G(x0 + v) - y0| ≤ (1 + ε)|L v| ≤ (1 + ε) · r/(1 + ε) = r.
 (6b) If x ∈ D, then x - x0 ∈ E_{r/(1-ε)}. Indeed x ∈ B by step 5, and (3b) with x' = x0 gives (1 - ε)|L(x - x0)| ≤ |G(x) - y0| ≤ r.

7. The images L(E_t) are balls of the plane T := range L. L is injective (step 2), so finrank T = finrank R^n = n (LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin). For t ≥ 0, L(E_t) = B_t(0) ∩ T:
 (⊆) L v ∈ T, and |L v| ≤ t means L v ∈ B_t(0);
 (⊇) if y = L v ∈ T with |y| ≤ t, then v ∈ E_t and y = L v.
 B_t(0) is closed, hence measurable, so H^n(B_t(0) ∩ T) = (H^n⌞T)(B_t(0)) (Measure.restrict_apply). By rsod_planeMeasure_closedBall (with n ≥ 1, the subspace T of dimension n, and s = t ≥ 0), H^n(L(E_t)) = ofReal(omega_n t^n).

8. Lipschitz images. Let f : R^{n+l} → R^{n+l} be K-Lipschitz on a set S, with K ∈ R_{≥0}. Then H^n(f(S)) ≤ K^n H^n(S). Indeed μHE[n] = c • μH[n] for a constant c (Measure.euclideanHausdorffMeasure_def), and μH[n](f(S)) ≤ K^n μH[n](S) (LipschitzOnWith.hausdorffMeasure_image_le with d = n ≥ 0, using K^(n:R) = K^n, ENNReal.rpow_natCast). Multiply by c. For K = toNNReal(a) with a ≥ 0 we have K^n = ofReal(a^n) (ENNReal.ofReal_pow). Also omega_n = π^{n/2}/Γ(n/2+1) ≥ 0.

9. Upper bound. Let Φ(w) := G(x0 + π(w)). Then Φ(L v) = G(x0 + v) for every v ∈ R^n.
 - Φ is (1 + ε)-Lipschitz on L(E_{r/(1-ε)}). For v, v' ∈ E_{r/(1-ε)}, step 6 (with t = r/(1 - ε) ≤ η0) gives x0 + v, x0 + v' ∈ B. By (3a), |Φ(L v) - Φ(L v')| = |G(x0 + v) - G(x0 + v')| ≤ (1 + ε)|L((x0 + v) - (x0 + v'))| = (1 + ε)|L v - L v'|.
 - G(D) ⊆ Φ(L(E_{r/(1-ε)})). For x ∈ D, v := x - x0 ∈ E_{r/(1-ε)} by (6b), and Φ(L v) = G(x0 + (x - x0)) = G(x).
 By step 5, monotonicity, step 8 and step 7 (with t = r/(1 - ε) ≥ 0):
 H^n(Γ ∩ B_r(y0)) = H^n(G(D)) ≤ H^n(Φ(L(E_{r/(1-ε)}))) ≤ (1 + ε)^n H^n(L(E_{r/(1-ε)})) = ofReal((1 + ε)^n) ofReal(omega_n (r/(1 - ε))^n) = ofReal(((1 + ε)^n/(1 - ε)^n) omega_n r^n).
 The last equality uses ENNReal.ofReal_mul (all factors are nonnegative) and (r/(1 - ε))^n = r^n/(1 - ε)^n.

10. Lower bound. Let Ψ(z) := L(π(z) - x0). Then Ψ(G(x)) = L(x - x0) for every x ∈ R^n.
 - Ψ is (1 - ε)^{-1}-Lipschitz on G(D). For x, x' ∈ D ⊆ B, (3b) gives |Ψ(G(x)) - Ψ(G(x'))| = |L(x - x0) - L(x' - x0)| = |L(x - x')| ≤ (1 - ε)^{-1}|G(x) - G(x')|.
 - L(E_{r/(1+ε)}) ⊆ Ψ(G(D)). For v ∈ E_{r/(1+ε)}, x0 + v ∈ D by (6a), and Ψ(G(x0 + v)) = L((x0 + v) - x0) = L v.
 By step 7 (with t = r/(1 + ε) ≥ 0), monotonicity and step 8:
 ofReal(omega_n (r/(1 + ε))^n) = H^n(L(E_{r/(1+ε)})) ≤ H^n(Ψ(G(D))) ≤ ofReal(((1 - ε)^{-1})^n) H^n(G(D)).
 Multiply both sides by ofReal((1 - ε)^n). On the right, ofReal((1 - ε)^n) ofReal(((1 - ε)^{-1})^n) = ofReal(((1 - ε)(1 - ε)^{-1})^n) = ofReal(1) = 1. On the left, ofReal((1 - ε)^n) ofReal(omega_n (r/(1 + ε))^n) = ofReal(((1 - ε)^n/(1 + ε)^n) omega_n r^n). This uses ENNReal.ofReal_mul and the nonnegativity of all factors. Hence ofReal(((1 - ε)^n/(1 + ε)^n) omega_n r^n) ≤ H^n(G(D)) = H^n(Γ ∩ B_r(y0)).

11. Steps 9 and 10 hold for every r with 0 < r ≤ η. Since y0 = graphPoint x0 (u x0) and Γ = graphOver u (ball 0 R), this is exactly the claim. ∎

Implementation aid (not part of the mathematical argument above). During decomposition, the following Lean proof of exactly this frozen statement compiled after `import GMT.Ch05.Submission`, inside `namespace GMT.Ch05` / `namespace Submission`, with the contract's `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal NNReal` and `open RectifiableVarifold` (Lean 4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d). It was compiled together with its sibling theorems and the assembled parent theorem, with no `sorry`; `#print axioms` reports only propext, Classical.choice and Quot.sound. It uses only the sibling theorems rsod_planeMeasure_closedBall and dohr_c1_uniform_first_order.

```lean
theorem dohr_c1_graph_mass_pinching : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (R : ℝ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 R) → ∀ x ∈ ball (0 : Rn n) R, ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, 0 < r → r ≤ η → ENNReal.ofReal ((1 - ε) ^ n / (1 + ε) ^ n * (unitBallVolume n * r ^ n)) ≤ (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) ∧ (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) ≤ ENNReal.ofReal ((1 + ε) ^ n / (1 - ε) ^ n * (unitBallVolume n * r ^ n)) := by
  intro n ℓ hn R u hu x₀ hx₀ ε hε hε1
  set P : Rn n →L[ℝ] Rn ℓ := fderiv ℝ u x₀ with hP
  have h1ε : 0 < 1 - ε := by linarith
  -- (1) Graph-coordinate algebra.
  have gp_sub : ∀ (x x' : Rn n) (y y' : Rn ℓ),
      graphPoint x y - graphPoint x' y' = graphPoint (x - x') (y - y') := by
    intro x x' y y'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [graphPoint]
  have gp_add : ∀ (x x' : Rn n) (y y' : Rn ℓ),
      graphPoint (x + x') (y + y') = graphPoint x y + graphPoint x' y' := by
    intro x x' y y'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [graphPoint]
  have gp_smul : ∀ (c : ℝ) (x : Rn n) (y : Rn ℓ),
      graphPoint (c • x) (c • y) = c • graphPoint x y := by
    intro c x y
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [graphPoint]
  have gp_norm : ∀ (x : Rn n) (y : Rn ℓ), ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp [graphPoint]
  have gp_le : ∀ (x : Rn n) (y : Rn ℓ), ‖x‖ ≤ ‖graphPoint x y‖ := fun x y =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      ((le_add_of_nonneg_right (sq_nonneg ‖y‖)).trans (gp_norm x y).ge)
  have gp_zero : ∀ y : Rn ℓ, ‖graphPoint (0 : Rn n) y‖ = ‖y‖ := by
    intro y
    have h := gp_norm 0 y
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
  -- (2) The first-coordinate projection and the tangent map `L v = (v, P v)`.
  let π : Amb n ℓ → Rn n := fun w => WithLp.toLp 2 (fun i : Fin n => w (Fin.castAdd ℓ i))
  have hπ : ∀ (x : Rn n) (y : Rn ℓ), π (graphPoint x y) = x := by
    intro x y
    ext i
    simp [π, graphPoint]
  let L : Rn n →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun v => graphPoint v (P v)
      map_add' := fun v w => by
        simp only [map_add]
        exact gp_add v w (P v) (P w)
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply]
        exact gp_smul c v (P v) }
  have hL : ∀ v, L v = graphPoint v (P v) := fun v => rfl
  have hLle : ∀ v, ‖v‖ ≤ ‖L v‖ := fun v => gp_le v (P v)
  have hLinj : Function.Injective L := by
    intro v w h
    have := hLle (v - w)
    rw [map_sub, h, sub_self, norm_zero] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hπL : ∀ v, π (L v) = v := fun v => hπ v (P v)
  let G : Rn n → Amb n ℓ := fun x => graphPoint x (u x)
  have hπG : ∀ x, π (G x) = x := fun x => hπ x (u x)
  have hGsub : ∀ x x', G x - G x' = graphPoint (x - x') (u x - u x') := fun x x' => gp_sub _ _ _ _
  have hGdist : ∀ x x', ‖x - x'‖ ≤ ‖G x - G x'‖ := by
    intro x x'
    rw [hGsub]
    exact gp_le _ _
  -- (3) First-order estimate on a closed ball `B = B_{η₀}(x₀)`.
  obtain ⟨η₀, hη₀, hB, hest⟩ :=
    dohr_c1_uniform_first_order n ℓ (ball 0 R) u isOpen_ball hu x₀ hx₀ ε hε
  have hGL : ∀ x ∈ closedBall x₀ η₀, ∀ x' ∈ closedBall x₀ η₀,
      ‖G x - G x' - L (x - x')‖ ≤ ε * ‖L (x - x')‖ := by
    intro x hx x' hx'
    have h1 : G x - G x' - L (x - x') = graphPoint 0 (u x - u x' - P (x - x')) := by
      rw [hGsub, hL, gp_sub, sub_self]
    rw [h1, gp_zero]
    exact (hest x hx x' hx').trans (mul_le_mul_of_nonneg_left (hLle _) hε.le)
  have hup : ∀ x ∈ closedBall x₀ η₀, ∀ x' ∈ closedBall x₀ η₀,
      ‖G x - G x'‖ ≤ (1 + ε) * ‖L (x - x')‖ := by
    intro x hx x' hx'
    calc ‖G x - G x'‖ = ‖(G x - G x' - L (x - x')) + L (x - x')‖ := by rw [sub_add_cancel]
      _ ≤ ‖G x - G x' - L (x - x')‖ + ‖L (x - x')‖ := norm_add_le _ _
      _ ≤ ε * ‖L (x - x')‖ + ‖L (x - x')‖ := by gcongr; exact hGL x hx x' hx'
      _ = (1 + ε) * ‖L (x - x')‖ := by ring
  have hlow : ∀ x ∈ closedBall x₀ η₀, ∀ x' ∈ closedBall x₀ η₀,
      (1 - ε) * ‖L (x - x')‖ ≤ ‖G x - G x'‖ := by
    intro x hx x' hx'
    have : ‖L (x - x')‖ ≤ ‖G x - G x'‖ + ‖G x - G x' - L (x - x')‖ := by
      calc ‖L (x - x')‖ = ‖(G x - G x') - (G x - G x' - L (x - x'))‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    nlinarith [hGL x hx x' hx']
  -- (4) Choice of `η`, localization and the (centred) ellipsoid sandwich.
  refine ⟨(1 - ε) * η₀, mul_pos h1ε hη₀, ?_⟩
  intro r hr hrη
  have hrη₀ : r / (1 - ε) ≤ η₀ := by rw [div_le_iff₀ h1ε]; linarith
  have hrη₀' : r / (1 + ε) ≤ η₀ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  let D : Set (Rn n) := ball 0 R ∩ G ⁻¹' closedBall (G x₀) r
  have hΓ : graphOver u (ball 0 R) ∩ closedBall (graphPoint x₀ (u x₀)) r = G '' D := by
    rw [graphOver, ← Set.image_inter_preimage]
  let E : ℝ → Set (Rn n) := fun t => {v | ‖L v‖ ≤ t}
  have hEB : ∀ t, t ≤ η₀ → ∀ v ∈ E t, x₀ + v ∈ closedBall x₀ η₀ := by
    intro t ht v hv
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact (hLle v).trans (le_trans hv ht)
  have hx₀B : x₀ ∈ closedBall x₀ η₀ := mem_closedBall_self hη₀.le
  have hDB : D ⊆ closedBall x₀ η₀ := by
    rintro x ⟨-, hx⟩
    rw [mem_preimage, mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall, dist_eq_norm]
    have : r ≤ η₀ := by nlinarith
    linarith [hGdist x x₀]
  have hED : ∀ v ∈ E (r / (1 + ε)), x₀ + v ∈ D := by
    intro v hv
    have hxB := hEB _ hrη₀' v hv
    refine ⟨hB hxB, ?_⟩
    rw [mem_preimage, mem_closedBall, dist_eq_norm]
    have h := hup (x₀ + v) hxB x₀ hx₀B
    rw [add_sub_cancel_left] at h
    have hv' : ‖L v‖ ≤ r / (1 + ε) := hv
    calc ‖G (x₀ + v) - G x₀‖ ≤ (1 + ε) * ‖L v‖ := h
      _ ≤ (1 + ε) * (r / (1 + ε)) := by gcongr
      _ = r := by field_simp
  have hDE : ∀ x ∈ D, x - x₀ ∈ E (r / (1 - ε)) := by
    intro x hx
    have hxB := hDB hx
    have hx2 : ‖G x - G x₀‖ ≤ r := by
      have := hx.2
      rwa [mem_preimage, mem_closedBall, dist_eq_norm] at this
    show ‖L (x - x₀)‖ ≤ r / (1 - ε)
    rw [le_div_iff₀ h1ε]
    linarith [hlow x hxB x₀ hx₀B]
  -- (5) The images `L(E_t)` are the closed `t`-balls of the `n`-plane `range L`.
  have hrank : Module.finrank ℝ (LinearMap.range L) = n := by
    rw [LinearMap.finrank_range_of_inj hLinj, finrank_euclideanSpace_fin]
  have hplane : ∀ t, 0 ≤ t →
      (μHE[n] : Measure (Amb n ℓ)) (L '' E t) = ENNReal.ofReal (unitBallVolume n * t ^ n) := by
    intro t ht
    have hset : L '' E t =
        closedBall (0 : Amb n ℓ) t ∩ ((LinearMap.range L : Submodule ℝ (Amb n ℓ)) : Set (Amb n ℓ)) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨mem_closedBall_zero_iff.2 hv, LinearMap.mem_range_self L v⟩
      · rintro ⟨hy, ⟨v, rfl⟩⟩
        exact ⟨v, mem_closedBall_zero_iff.1 hy, rfl⟩
    rw [hset, ← Measure.restrict_apply measurableSet_closedBall]
    exact rsod_planeMeasure_closedBall n ℓ hn (LinearMap.range L) hrank t ht
  -- (6) Lipschitz images and `Hⁿ`.
  have hlip : ∀ (K : ℝ≥0) (f : Amb n ℓ → Amb n ℓ) (s : Set (Amb n ℓ)), LipschitzOnWith K f s →
      (μHE[n] : Measure (Amb n ℓ)) (f '' s) ≤ (K : ℝ≥0∞) ^ n * (μHE[n] : Measure (Amb n ℓ)) s := by
    intro K f s hf
    have h := hf.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [ENNReal.rpow_natCast] at h
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply,
      ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
    calc _ ≤ _ * ((K : ℝ≥0∞) ^ n * μH[(n : ℝ)] s) := by gcongr
      _ = _ := by ring
  have hpow : ∀ c : ℝ, 0 ≤ c → ((Real.toNNReal c : ℝ≥0) : ℝ≥0∞) ^ n = ENNReal.ofReal (c ^ n) :=
    fun c hc => (ENNReal.ofReal_pow hc n).symm
  have hω : 0 ≤ unitBallVolume n := by
    unfold unitBallVolume
    exact div_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (Real.Gamma_pos_of_pos (by positivity)).le
  rw [hΓ]
  constructor
  · -- Lower bound via `Ψ(z) = L(π z - x₀)`, which is `(1 - ε)⁻¹`-Lipschitz on `G(D)`.
    let Ψ : Amb n ℓ → Amb n ℓ := fun z => L (π z - x₀)
    have hΨlip : LipschitzOnWith (Real.toNNReal (1 - ε)⁻¹) Ψ (G '' D) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
      simp only [Ψ, hπG]
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right,
        Real.coe_toNNReal _ (inv_nonneg.2 h1ε.le)]
      rw [inv_mul_eq_div, le_div_iff₀ h1ε, mul_comm]
      exact hlow x (hDB hx) x' (hDB hx')
    have himg : L '' E (r / (1 + ε)) ⊆ Ψ '' (G '' D) := by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨G (x₀ + v), ⟨x₀ + v, hED v hv, rfl⟩, ?_⟩
      simp only [Ψ, hπG, add_sub_cancel_left]
    have h1 : (μHE[n] : Measure (Amb n ℓ)) (L '' E (r / (1 + ε))) ≤
        ((Real.toNNReal (1 - ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n * (μHE[n] : Measure (Amb n ℓ)) (G '' D) :=
      (measure_mono himg).trans (hlip _ _ _ hΨlip)
    rw [hplane _ (by positivity), hpow _ (inv_nonneg.2 h1ε.le)] at h1
    have key : ENNReal.ofReal ((1 - ε) ^ n / (1 + ε) ^ n * (unitBallVolume n * r ^ n)) =
        ENNReal.ofReal ((1 - ε) ^ n) * ENNReal.ofReal (unitBallVolume n * (r / (1 + ε)) ^ n) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_pow]
      field_simp
    rw [key]
    calc ENNReal.ofReal ((1 - ε) ^ n) * ENNReal.ofReal (unitBallVolume n * (r / (1 + ε)) ^ n)
        ≤ ENNReal.ofReal ((1 - ε) ^ n) *
            (ENNReal.ofReal ((1 - ε)⁻¹ ^ n) * (μHE[n] : Measure (Amb n ℓ)) (G '' D)) := by
          gcongr
      _ = (μHE[n] : Measure (Amb n ℓ)) (G '' D) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
            mul_inv_cancel₀ h1ε.ne', one_pow, ENNReal.ofReal_one, one_mul]
  · -- Upper bound via `Φ(w) = G(x₀ + π w)`, which is `(1 + ε)`-Lipschitz on `L(E_{r/(1-ε)})`.
    let Φ : Amb n ℓ → Amb n ℓ := fun w => G (x₀ + π w)
    have hΦlip : LipschitzOnWith (Real.toNNReal (1 + ε)) Φ (L '' E (r / (1 - ε))) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩
      simp only [Φ, hπL]
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, Real.coe_toNNReal _ (by linarith)]
      have h := hup (x₀ + v) (hEB _ hrη₀ v hv) (x₀ + v') (hEB _ hrη₀ v' hv')
      rwa [add_sub_add_left_eq_sub] at h
    have himg : G '' D ⊆ Φ '' (L '' E (r / (1 - ε))) := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨L (x - x₀), ⟨x - x₀, hDE x hx, rfl⟩, ?_⟩
      simp only [Φ, hπL, add_sub_cancel]
    have h1 : (μHE[n] : Measure (Amb n ℓ)) (G '' D) ≤
        ((Real.toNNReal (1 + ε) : ℝ≥0) : ℝ≥0∞) ^ n *
          (μHE[n] : Measure (Amb n ℓ)) (L '' E (r / (1 - ε))) :=
      (measure_mono himg).trans (hlip _ _ _ hΦlip)
    rw [hplane _ (by positivity), hpow _ (by linarith)] at h1
    refine h1.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow]
    field_simp
```

## Key steps

1. graph coordinates: (x, y) is linear, |(x,y)|^2 = |x|^2 + |y|^2 and π(x, y) = x; L v = (v, Du(x0) v) is injective with |v| <= |L v|
2. dohr_c1_uniform_first_order gives (1-ε)|L(x-x')| <= |G(x)-G(x')| <= (1+ε)|L(x-x')| on B = closed B_{η0}(x0); take η = (1-ε)η0
3. for 0 < r <= η: Γ ∩ B_r(y0) = G(D) with D ⊆ B, x0 + E_{r/(1+ε)} ⊆ D and D - x0 ⊆ E_{r/(1-ε)}, where E_t = {v : |L v| <= t}
4. L(E_t) = B_t(0) ∩ range L with dim range L = n, so H^n(L(E_t)) = omega_n t^n by rsod_planeMeasure_closedBall
5. H^n(f(S)) <= K^n H^n(S) for K-Lipschitz f, applied to Φ(w) = G(x0 + π w) (K = 1+ε, upper bound) and Ψ(z) = L(π z - x0) (K = (1-ε)^{-1}, lower bound)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean (identical); diff GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean (identical)`
- `rg -n 'theorem LipschitzOnWith.hausdorffMeasure_image_le|theorem hausdorffMeasure_image_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n norm_image_sub_le_of_norm_hasFDerivWithin_le <snapshot>/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `rg -n 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen' <snapshot>/mathlib/Mathlib/Analysis/Calculus/ContDiff/*.lean`
- `rg -n finrank_range_of_inj <snapshot>/mathlib/Mathlib/LinearAlgebra`
- `rg -n 'theorem MeasureTheory.Measure.euclideanHausdorffMeasure_def|theorem InnerProductSpace.euclideanHausdorffMeasure_eq_volume|theorem Isometry.map_euclideanHausdorffMeasure' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem restrict_apply \(' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean; rg -n 'theorem tendsto_order ' <snapshot>/mathlib/Mathlib/Topology/Order/Basic.lean; rg -n 'theorem addHaar_closedBall ' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean; rg -n 'theorem image_inter_preimage' <snapshot>/mathlib/Mathlib/Data/Set/Image.lean`
- `rg -n 'noncomputable def normDet|theorem euclideanHausdorffMeasure_image_eq_normDet_mul_volume' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean; rg -n volume_closedBall <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `sed -n 1,200p .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean (areaJacobianWithin, ae_fderivWithin_eq_of_lipschitz_extension, injective_area_formula_lipschitzOn); sed -n 1,80p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (imports)`
- `lake env lean -o /tmp/c1gd-v2/build/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/c1gd-v2/build lean /tmp/c1gd-v2/src/Avail.lean' (#check LipschitzOnWith.hausdorffMeasure_image_le, Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le, ContDiffOn.continuousOn_fderiv_of_isOpen, LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin, Measure.restrict_apply, Measure.euclideanHausdorffMeasure_def, ENNReal.rpow_natCast, Ioc_mem_nhdsGT, tendsto_order)`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/c1gd-v2/build lean /tmp/c1gd-v2/src/Unavail.lean' (#check LinearMap.normDet, Poincare.SimonGMT.Chapter02.injective_area_formula_lipschitzOn, InnerProductSpace.volume_closedBall, EuclideanSpace.volume_closedBall, LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume)`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/c1gd-v2/build lean /tmp/c1gd-v2/src/Full.lean' (all 4 child proofs + parent assembly; #print axioms)`
- `lake env lean --root=/tmp/c1gd-v2/sim -o /tmp/c1gd-v2/build2/GMT/Ch05/Submission.olean /tmp/c1gd-v2/sim/GMT/Ch05/Submission.lean (Submission copy with the 5 proofs in namespace Submission)`
- `python3 -I /tmp/c1gd-v2/scripts/nodemods.py (verifier gmt-compare.py contract_scope/child_modules, mode contract); lean NodeChallenge.lean against /tmp/c1gd-v2/build and NodeSolution.lean + '#print axioms HumanizeNodeComparator.target' against /tmp/c1gd-v2/build2 for all 5 statements`
- `python3 -I /tmp/c1gd-v2/scripts/mkstmts.py (verifier lean_contract.validate_lean_statement on the 4 statements; lean_name ownership in dag.json; rsod_planeMeasure_closedBall type copied from dag.json)`
- `python3 -I (dag.json): list id | lean_name | status for all nodes (200, re-read later: 217); print lean_statement of all 68 accepted checkpoints`
- `git -C .swarm-worktrees/7b984ce372887989aaee/gmt-ch05 show 7881dde:GMT/Ch05/Submission.lean (accepted proof of rsod_planeMeasure_closedBall)`
- `ls -d .swarm-worktrees/*/gmt-ch05/GMT/Ch05 | xargs -P 16 grep -lr -E 'dohr_c1_uniform_first_order|dohr_c1_graph_mass_pinching|dohr_ratio_tendsto_one_of_pinching' (1000 worktrees: no match); grep -rl same names lake-packages-25730c7c/simongmt/Poincare (no match)`
- `sed -n 1793,1990p and 6503,6545p /runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py (_solve_children reuse of accepted checkpoints and node bound; _existing_lean_name_problem); python3 -I: .humanize/swarm-configs/* with github_selected_issue 476 (max_nodes 1000)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-c1-graph-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-c1-graph-density-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-c1-graph-density-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-tangent-plane-ae-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/math-wiki/submission-rsod-planemeasure-closedball.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py`
- `/tmp/c1gd-v2/src/Avail.lean`
- `/tmp/c1gd-v2/src/Unavail.lean`
- `/tmp/c1gd-v2/src/Full.lean`
- `/tmp/c1gd-v2/sim/GMT/Ch05/Submission.lean`
- `/tmp/c1gd-v2/nodes/graph_mass_pinching/NodeChallenge.lean`
- `/tmp/c1gd-v2/nodes/graph_mass_pinching/NodeSolution.lean`
- `/tmp/c1gd-v2/final/stmts.json`

Pinned snapshot (manifest.json): project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Contract.lean is byte-identical to the workspace Contract.lean, and the workspace Submission.lean is still a byte copy of the contract. Usable under the frozen imports (snapshot line numbers): LipschitzOnWith.hausdorffMeasure_image_le (Hausdorff.lean l.733), Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (MeanValue.lean l.422), ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean l.916), LinearMap.finrank_range_of_inj (Dimension/Finrank.lean l.127), euclideanHausdorffMeasure_def / Isometry.map_euclideanHausdorffMeasure / InnerProductSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean l.74/141/191), Measure.restrict_apply (Restrict.lean l.75), tendsto_order (Topology/Order/Basic.lean l.139), addHaar_closedBall (EqHaar.lean l.500) and Set.image_inter_preimage (Image.lean l.454). Not reachable: LinearMap.normDet and euclideanHausdorffMeasure_image_eq_normDet_mul_volume (NormDet.lean l.69/433), InnerProductSpace/EuclideanSpace.volume_closedBall (VolumeOfBalls.lean l.354/324) and simongmt Chapter02.injective_area_formula_lipschitzOn (AreaDomain.lean); Lean reports unknown constants/identifiers. This forces the supplied step 6 to be replaced by Lipschitz-image comparisons. Reuse: Submission.rsod_planeMeasure_closedBall is an accepted checkpoint (status accepted, candidate commit 7881dde5f7e308e54f05a8f95dc7a4b94e277e4c, math-wiki page). Its proof is import-free (it computes the unit-ball volume by Gaussian integrals). Its frozen type is copied byte-identically from dag.json, and runtime.py maps a child with that lean_name to the existing node. No match: dohr_c1_uniform_first_order, dohr_c1_graph_mass_pinching and dohr_ratio_tendsto_one_of_pinching occur nowhere in dag.json, the 1000 swarm worktrees or simongmt; the only other relevant prior artifact is this node's own unpublished decomposition-v1 (audited acceptable). Lean checks: all four child types pass validate_lean_statement and elaborate in the verifier-generated NodeChallenge modules against the frozen Submission. Full proofs of the four children and of the parent assembly compile; the NodeSolution checks `exact Submission.X` pass for all five; the axioms are only propext, Classical.choice and Quot.sound. The issue-476 worker configuration allows max_nodes = 1000 (217 nodes at the last re-read), so the three new nodes fit.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
