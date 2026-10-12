<!-- theorem-id: gmt-ch05/root.lipschitz_approximation-a1.tangent_structure-a1 -->

## Theorem `Submission.lip_approx_tangent_structure`

Let n >= 1, l in N, U open in R^(n+l), V = v(M, theta) a contract RectifiableVarifold in U, mu = V.weight and p_x = V.tangentProj x. Then (a) x -> p_x is mu-a.e. strongly measurable; (b) for every linear subspace T and every compact K contained in U, x -> hsNormSq(p_x - p_T) is mu-integrable on K; (c) for mu-a.e. x, p_x is the orthogonal projection onto some n-dimensional subspace, and mu(B_r(x))/(omega_n r^n) -> theta(x) as r -> 0+ (V.HasDensity x (V.mult x)).

Node: `root.lipschitz_approximation-a1.tangent_structure-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/114

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/653, https://github.com/ZhengyangZhang06/gmt-formalize/issues/796, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1407

## Lean problem

Declaration: `Submission.lip_approx_tangent_structure`

```lean
∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight ∧ (∀ (T : Submodule ℝ (Amb n ℓ)) (K : Set (Amb n ℓ)), IsCompact K → K ⊆ U → IntegrableOn (fun x => hsNormSq (V.tangentProj x - T.starProjection)) K V.weight) ∧ ∀ᵐ x ∂V.weight, (∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ V.tangentProj x = T.starProjection) ∧ V.HasDensity x (V.mult x)
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

- Parent DAG node: `root.lipschitz_approximation-a1`
- Child DAG node: `root.lipschitz_approximation-a1.tangent_structure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 2, Theorem 1.5 (C^1 Approximation Theorem) and its printed proof (Rademacher 1.4, Lusin, Egoroff, closed subset, Whitney extension theorem 1.6); Simon Ch. 3, Lemma 1.2 ("only if"), Remark 1.3, the proof of Theorem 1.6 ("=>"), Remarks 1.5(3), 1.8(1), 1.8(2) and Theorem 1.9; specialised to the contract's RectifiableVarifold and tangentProj. This is fact (F1) of the parent proof. Part A proves the C^1 approximation theorem (it is not cited). It constructs closed sets of almost full measure on which the derivative is continuous and the Taylor remainders are uniformly small on compacts. It then verifies the three hypotheses of the checked Whitney theorem and tracks the exceptional measure through the componentwise application.

Notation. M := V.carrier (contained in U), theta := V.mult (theta > 0 on M), H^n := muHE[n], mu := V.weight, so mu(A) = integral_(A cap M) theta dH^n for H^n-measurable A. On R^n, H^n equals Lebesgue measure L^n = volume (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume). B_r(x) is the closed ball, B^o_r(x) the open ball. eta_(x,r)(z) := r^-1 (z - x) (SimonGMT blowUpMap). For an n-dimensional subspace T, p_T := T.starProjection. "T is a weighted approximate tangent plane of (M, theta) at x" means HasWeightedApproximateTangentSpaceAt n M theta x T: finrank T = n and, for every f in C_c(R^(n+l)), integral_(eta_(x,r)(M)) f(y) theta(x + r y) dH^n(y) -> theta(x) integral_T f dH^n as r -> 0+. By definition p_x := V.tangentProj x is p_P for the plane P chosen by Classical.choose when such a plane exists, and 0 otherwise. omega_n := unitBallVolume n = pi^(n/2)/Gamma(n/2 + 1). For a map f, Df(x) := fderiv R f x (Mathlib's Frechet derivative, 0 where f is not differentiable). For 0 < eps < 1 let f_eps, g_eps in C_c(R^(n+l), [0,1]) be radial and piecewise linear in |y|, with f_eps = 1 on B_1(0), f_eps = 0 off B_(1+eps)(0), g_eps = 1 on B_(1-eps)(0), g_eps = 0 off B^o_1(0); then g_eps <= indicator of B_1(0) <= f_eps.

Checked tools. These come from the pinned Mathlib and the pinned SimonGMT. All are sorry-free and use only the axioms propext, Classical.choice and Quot.sound.
(Rad) Rademacher. A Lipschitz map between finite-dimensional real spaces is differentiable L^n-a.e. (Mathlib LipschitzWith.ae_differentiableAt). For any map f, the differentiability set is Borel, and x -> Df(x) and x -> Df(x)v are Borel (Mathlib measurableSet_of_differentiableAt, measurable_fderiv, measurable_fderiv_apply_const). If f is Lambda-Lipschitz, then ||Df(x)|| <= Lambda (Mathlib norm_fderiv_le_of_lipschitz).
(Eg) Egorov (Mathlib tendstoUniformlyOn_of_ae_tendsto). Let S be a measurable set of finite measure and h_k strongly measurable real functions with h_k -> h at every point of S. For every tau > 0 there is a measurable t contained in S with measure <= tau such that h_k -> h uniformly on S minus t.
(Lu) Lusin (SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable). Let nu be a measure on R^d such that every measurable set S with nu(S) < infinity contains, for every tau > 0, a closed F with nu(S minus F) < tau. If A is measurable with nu(A) < infinity, h : R^d -> R is Borel and tau > 0, then there is a closed C contained in A with nu(A minus C) < tau and h restricted to C continuous. The hypothesis on nu holds in two cases. For nu = L^n, Lebesgue measure is weakly regular (Mathlib MeasurableSet.exists_isClosed_sdiff_lt). For every finite Borel measure on R^(n+l), finite measures on metric spaces are weakly regular.
(Wh) Whitney (SimonGMT Chapter02.exists_contDiff_one_extension_of_whitney). Let A be a closed subset of R^n, h : R^n -> R and D : R^n -> (R^n ->L[R] R) with HasWhitneyC1Compatibility A h D, i.e.
 (W1) ContinuousOn h A;
 (W2) ContinuousOn D A;
 (W3) for every compact K contained in A and every tau > 0 there is delta > 0 with |h(y) - h(x) - D(x)(y - x)| <= tau |y - x| whenever x in K, y in A and |x - y| < delta.
 Then there is g : R^n -> R with ContDiff R 1 g, g = h on A, and HasFDerivAt g (D a) a for every a in A.
(S) Scaling. eta_(x,r) is a similarity with ratio 1/r, so H^n(eta_(x,r)(E)) = r^-n H^n(E) (Mathlib hausdorffMeasure_homothety_image and isometry invariance). Equivalently, the image of H^n restricted to E under eta_(x,r) is r^n times H^n restricted to eta_(x,r)(E). Hence integral_(eta_(x,r)(E)) h dH^n = r^-n integral_E h((z - x)/r) dH^n(z) for H^n-measurable E and measurable h >= 0. For signed h, h is integrable on eta_(x,r)(E) iff z -> h((z - x)/r) is integrable on E, and then the same identity holds. In particular, let f in C_c vanish off B_R(0) and let r be so small that B_(rR)(x) is contained in U. Then, by (L), both sides of integral_(eta_(x,r)(M)) f(y) theta(x + r y) dH^n(y) = r^-n integral f((z - x)/r) dmu(z) are finite and equal, since mu = theta H^n restricted to M (Mathlib integral_withDensity_eq_integral_toReal_smul₀ for the right side; theta is a.e.-measurable). Only such small r matter for the limits r -> 0+ below.
(L) Local finiteness. For compact K contained in U, mu(K) = integral_(M cap K) theta dH^n < infinity (V.integrableOn_mult). U is the union of the open sets U_m := {x : |x| < m, infEdist(x, complement of U) > 1/m} (m >= 1; infEdist to the empty set is +infinity). The closure of each U_m is compact and contained in U.
(UD) Upper density theorem (Simon Ch. 1, 3.6; SimonGMT Chapter01.simon_theorem_3_6 and its a.e. form Chapter01.ae_dimensionalUpperDensity_eq_zero_outside). Let lambda be a measure on R^(n+l) whose outer measure is Borel regular; this holds for every Mathlib measure on R^(n+l) (SimonGMT Chapter01.measure_toOuterMeasure_isBorelRegular). Let A be lambda-null-measurable with lambda(A) < infinity. Then limsup_(r -> 0) r^-n lambda(A cap B_r(x)) = 0 for H^n-a.e. x not in A.
 - Null-measurable sets are Caratheodory measurable for the outer measure: take a measurable T containing A with A = T lambda-a.e.; T is Caratheodory measurable, and lambda(t cap A) = lambda(t cap T), lambda(t minus A) = lambda(t minus T) for every t.
 - SimonGMT states the null set for simonHausdorffOuterMeasureReal n, which is the outer measure of simonHausdorffMeasureReal n (Chapter01.simonHausdorffMeasureReal_toOuterMeasure). Moreover simonHausdorffMeasureReal n = c_n H^n with 0 < c_n < infinity (Chapter02.simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure, simonAreaNormalization_pos, simonAreaNormalization_ne_top). So its null sets are exactly the H^n-null sets.
 - Its density quotient lambda(A cap B_r(x))/(realUnitBallVolume n * ofReal(r)^(n:R)) is r^-n lambda(A cap B_r(x)) times a positive constant (ofReal(r)^(n:R) = r^n by ENNReal.rpow_natCast), so the two quantities vanish together.
(AF) Area formula (SimonGMT Chapter02).
 (i) For every map G : R^n -> R^N, H^n(G({v : G is differentiable at v and DG(v) is not injective})) = 0 (area_image_criticalSet_eq_zero).
 (ii) Let s be a Borel subset of R^n, and let G be differentiable at every point of s, with injective derivative there, and injective on s. Then integral_(G(s)) h dH^n = integral_s JG(v) h(G(v)) dv for every h >= 0, where JG(v) = areaJacobianAt G v = (det(DG(v)^T DG(v)))^(1/2) (weighted_area_formula_volume_of_injective_derivative).
 (iii) A K-Lipschitz map on a set A multiplies H^n(A) by at most K^n (euclideanHausdorffMeasure_image_le_of_lipschitzOn). In particular, Lipschitz maps send L^n-null sets to H^n-null sets.

Part A. C^1 approximation (Simon Ch. 2, Theorem 1.5).
Claim A. Let n >= 1, N >= 0, F : R^n -> R^N Lipschitz and eps > 0. Then there is a C^1 map G : R^n -> R^N with L^n({x : F(x) != G(x)}) < eps.
Steps A1-A5 prove the scalar case. Let f : R^n -> R be Lambda-Lipschitz and eps > 0. We construct a closed set A with L^n(R^n minus A) < eps and a C^1 function g with g = f on A; moreover f and g are both differentiable at each a in A with derivative Df(a). The steps follow the printed proof (Rademacher, Lusin, Egoroff, closed subset, Whitney), with two refinements. First, L^n is infinite, so Lusin and Egoroff are applied on bounded pieces, which are then glued by local finiteness. Second, the remainder supremum is taken over all y (not only over y in the Lusin set) and computed on a countable dense set, which makes it Borel.
A1. Rademacher. Let B := {x : f is differentiable at x} and D := Df. Let e_1, ..., e_n be a basis of R^n and D_i(x) := D(x)e_i. By (Rad):
 - B is Borel and L^n(R^n minus B) = 0;
 - D and each D_i are Borel;
 - ||D(x)|| <= Lambda for all x;
 - f has Frechet derivative D(x) at every x in B.
A2. Remainder functions. For x != y put R(x,y) := |f(y) - f(x) - D(x)(y - x)| / |y - x|, and R(x,x) := 0. Then 0 <= R <= 2 Lambda, since |f(y) - f(x)| <= Lambda |y - x| and |D(x)(y - x)| <= Lambda |y - x|. Fix a countable dense set Q in R^n (Mathlib TopologicalSpace.exists_countable_dense). For k in N and q in Q, let phi_(k,q)(x) := R(x,q) if 0 < |q - x| < 1/(k+1), and phi_(k,q)(x) := 0 otherwise. Let Rsup_k(x) := sup_(q in Q) phi_(k,q)(x), which lies in [0, 2 Lambda].
 (i) Rsup_k is Borel. The set {x : 0 < |q - x| < 1/(k+1)} is Borel. The map x -> R(x,q) is Borel, because f is continuous, D is Borel and (L, v) -> L v is continuous. So each phi_(k,q) is Borel, and a countable supremum of Borel real functions is Borel (Mathlib Measurable.iSup). In particular Rsup_k is strongly measurable.
 (ii) Rsup_k(x) -> 0 for every x in B. Given tau > 0, differentiability at x gives r > 0 with |f(y) - f(x) - D(x)(y - x)| <= (tau/2) |y - x| for |y - x| < r. If 1/(k+1) < r, every phi_(k,q)(x) is either 0 or R(x,q) <= tau/2, so 0 <= Rsup_k(x) <= tau/2 < tau.
 (iii) If 0 < |y - x| < 1/(k+1), then R(x,y) <= Rsup_k(x). Suppose instead Rsup_k(x) < R(x,y). The functions z -> |z - x| and z -> R(x,z) are continuous at y (as y != x). So there is r > 0 such that every z with |z - y| < r satisfies 0 < |z - x| < 1/(k+1) and R(x,z) > Rsup_k(x). Since Q is dense, some q in Q has |q - y| < r, and then Rsup_k(x) >= phi_(k,q)(x) = R(x,q) > Rsup_k(x), a contradiction.
A3. Egoroff and Lusin on bounded pieces. For m in N let S_m := B cap {x : m <= |x| < m + 1}. The S_m are Borel and pairwise disjoint, L^n(S_m) <= L^n(B_(m+1)(0)) < infinity, and B is the union of the S_m. Choose eps_m > 0 with sum_m eps_m < eps (Mathlib ENNReal.exists_pos_sum_of_countable). Fix m.
 (a) Egoroff. Apply (Eg) on S_m to Rsup_k -> 0. The convergence holds at every point of S_m, which is contained in B, by A2(ii), and Rsup_k is strongly measurable by A2(i). This gives a Borel t_m contained in S_m with L^n(t_m) <= eps_m/2 such that Rsup_k -> 0 uniformly on S_m minus t_m.
 (b) Lusin. Apply (Lu) with nu = L^n on the Borel set S_m minus t_m, which has finite measure, to the Borel functions D_1, ..., D_n with tolerance eps_m/(2n) each. This gives closed sets C_(m,i) contained in S_m minus t_m with L^n((S_m minus t_m) minus C_(m,i)) < eps_m/(2n) and D_i continuous on C_(m,i).
 (c) Let K_m := C_(m,1) cap ... cap C_(m,n); as n >= 1, K_m is contained in C_(m,1). Then:
 - K_m is closed and contained in S_m minus t_m, hence in B cap {m <= |x| < m + 1}, so K_m is compact;
 - every D_i is continuous on K_m, so D is continuous on K_m: for v = sum_i v_i e_i we have D(x)v = sum_i v_i D_i(x), and a map into the finite-dimensional space of linear maps is continuous on a set iff all its evaluations are (Mathlib continuousOn_clm_apply);
 - Rsup_k -> 0 uniformly on K_m;
 - S_m minus K_m is contained in t_m union the union over i of ((S_m minus t_m) minus C_(m,i)), so L^n(S_m minus K_m) <= eps_m/2 + n eps_m/(2n) = eps_m.
A4. The closed set A := union over m of K_m.
 (a) A is closed. The family (K_m) is locally finite, because the open ball B^o_1(x) meets K_m only if m < |x| + 1. A locally finite union of closed sets is closed (Mathlib LocallyFinite.isClosed_iUnion).
 (b) L^n(R^n minus A) < eps. If x is not in A, then either x is not in B, or x lies in S_m minus K_m for m = floor(|x|). Hence L^n(R^n minus A) <= L^n(R^n minus B) + sum_m L^n(S_m minus K_m) <= 0 + sum_m eps_m < eps.
 (c) A is contained in B, so f has derivative D(a) at each a in A.
 (d) D is continuous on A. Let a lie in K_m, and let W := the union over j != m of K_j. W is closed, being a locally finite union of closed sets. Also a is not in W, since the K_j lie in the pairwise disjoint shells {j <= |x| < j + 1}. So the complement of W is a neighbourhood of a whose intersection with A is contained in K_m. Thus K_m is a neighbourhood of a relative to A, and continuity of D restricted to K_m at a gives continuity of D restricted to A at a (Mathlib ContinuousWithinAt.mono_of_mem_nhdsWithin).
 (e) Compact-uniform Taylor remainder. Let K be a compact subset of A and tau > 0. Then K is contained in B_(r_K)(0) for some r_K >= 0, so K is contained in K_0 union ... union K_(floor(r_K)). By A3(c) applied to these finitely many sets, there is k with Rsup_k(x) < tau for every x in K. Put delta := 1/(k+1) > 0, and let x in K and y in A with |x - y| < delta. If y = x, both sides of the inequality in (W3) vanish. Otherwise 0 < |y - x| < 1/(k+1), and A2(iii) gives |f(y) - f(x) - D(x)(y - x)| = R(x,y) |y - x| <= Rsup_k(x) |y - x| <= tau |y - x|.
A5. Whitney. By A4, A is closed, and the three hypotheses hold for h := f and D:
 - (W1): f is Lipschitz, hence continuous;
 - (W2): this is A4(d);
 - (W3): this is A4(e).
 That is, HasWhitneyC1Compatibility A f D holds. (Wh) gives g in C^1(R^n) with g = f on A and Dg(a) = D(a) for a in A. Hence {f != g} is contained in R^n minus A, which has L^n-measure < eps. Moreover, by A4(c), {f != g} union {x : f does not have derivative Dg(x) at x} is also contained in R^n minus A; this is Simon's form of Theorem 1.5.
A6. Componentwise application and the exceptional measure. Let F : R^n -> R^N be Lambda-Lipschitz and eps > 0. If N = 0, take G := F, since R^0 is a point. Otherwise choose eps_1, ..., eps_N > 0 with sum_j eps_j < eps. Each coordinate F^j(x) := F(x)_j is Lambda-Lipschitz, since |F(x)_j - F(y)_j| <= |F(x) - F(y)| (Mathlib PiLp.norm_apply_le). A1-A5 with tolerance eps_j give closed A_j with L^n(R^n minus A_j) < eps_j and C^1 functions g^j with g^j = F^j on A_j. Put G(x) := (g^1(x), ..., g^N(x)). G is C^1 because all its coordinates are (Mathlib contDiff_euclidean). If F(x) != G(x), then F^j(x) != g^j(x) for some j, so x is not in A_j. Therefore {F != G} is contained in the union over j of (R^n minus A_j), and L^n({F != G}) <= sum_j L^n(R^n minus A_j) < sum_j eps_j < eps. This proves Claim A.
 Remark: A1-A6 compile in Lean against the pinned Mathlib and SimonGMT, with axioms propext, Classical.choice and Quot.sound (scratch file /tmp/lipapprox-dec-v2/c1a/C1A.lean, theorems C1ACheck.c1_approx_scalar and C1ACheck.c1_approx). The Lean version also intersects with a Lusin set for the zero function, so that K_m stays inside S_m minus t_m even for n = 0. Whitney is used through a verbatim copy of SimonGMT Chapter02/WhitneyExtension.lean. A final formalization can import Poincare.SimonGMT.Chapter02.WhitneyExtension directly: it is sorry-free, but not prebuilt in the package, so Lake builds it on first use.

Part B. C^1 cover of M (Simon Ch. 3, Lemma 1.2 "only if", and Remark 1.3).
B1. By V.countablyRectifiable, M is contained in M_0 union the union over j of F_j(R^n), with H^n(M_0) = 0 and F_j : R^n -> R^(n+l) Lipschitz. For all j, i >= 1, Claim A (N = n + l, eps = 1/i) gives a C^1 map G_ij : R^n -> R^(n+l) with L^n({F_j != G_ij}) < 1/i.
 Then Z_j := the intersection over i of {F_j != G_ij} has L^n(Z_j) <= 1/i for every i, so L^n(Z_j) = 0. By (AF)(iii), H^n(F_j(Z_j)) = 0, since F_j is Lipschitz and H^n = L^n on R^n. Every v not in Z_j satisfies F_j(v) = G_ij(v) for some i, so F_j(R^n) is contained in F_j(Z_j) union the union over i of G_ij(R^n).
B2. Fix one of the C^1 maps G := G_ij and let O := {v : DG(v) is injective}.
 - O is open: if DG(u) is injective, then c_u := min_(|w|=1) |DG(u)w| > 0, every linear map L with ||L - DG(u)|| < c_u is injective, and DG is continuous.
 - G(R^n minus O) is H^n-null by (AF)(i), since G is differentiable everywhere and R^n minus O is its critical set.
 - For u in O choose sigma_u > 0 with B_(sigma_u)(u) contained in O and ||DG(v) - DG(u)|| <= c_u/2 for |v - u| <= sigma_u. The mean value inequality (Mathlib Convex.norm_image_sub_le_of_norm_fderiv_le) applied to v -> G(v) - DG(u)v on the convex ball gives |G(v) - G(v') - DG(u)(v - v')| <= (c_u/2) |v - v'|. Hence |G(v) - G(v')| >= (c_u/2) |v - v'| for v, v' in B^o_(sigma_u)(u).
 - By the Lindelof property of R^n, countably many such open balls cover O.
B3. Enumerate over all (j, i) and all chosen balls by k >= 1. This is a countable family; if it is finite, pad it with the empty ball B_k := B^o_0(0) and G_k := v -> graphPoint v 0, so that N_k is empty and all properties below hold vacuously. We obtain: M is contained in N_0 union the union over k >= 1 of N_k, where:
 - N_0 is a Borel set with H^n(N_0) = 0: a Borel H^n-null superset (Mathlib toMeasurable) of the null set M_0 union the F_j(Z_j) union the G_ij(R^n minus O_ij);
 - N_k = G_k(B_k), with B_k an open ball of R^n, G_k : R^n -> R^(n+l) of class C^1, and c_k > 0 such that |G_k(v) - G_k(v')| >= c_k |v - v'| for v, v' in B_k.
 Consequently:
 - G_k is injective on B_k, and DG_k(v) is injective for v in B_k;
 - G_k restricted to B_k is a homeomorphism onto N_k, since its inverse is (1/c_k)-Lipschitz;
 - N_k is sigma-compact (B_k is a countable union of closed balls), hence Borel;
 - DG_k is bounded on B_k (continuous on the compact closure), so G_k is Lipschitz on the convex set B_k, and H^n(N_k) <= (Lip of G_k on B_k)^n L^n(B_k) < infinity by (AF)(iii).
B4. Put M'_0 := M cap N_0 and M'_k := (M cap N_k) minus (N_0 union N_1 union ... union N_(k-1)) for k >= 1. These sets:
 - are pairwise disjoint;
 - are H^n-null-measurable (M is, by V.nullMeasurableSet_carrier, and the N_k are Borel);
 - cover M, with H^n(M'_0) = 0 and M'_k contained in N_k.
 This is the construction of SimonGMT Chapter03.simon_remark_1_3_nullMeasurable.

Part C. Blow-ups of N_k (k >= 1). For x = G_k(u) in N_k, let T_x N_k := DG_k(u)(R^n), an n-dimensional subspace.
C1. Claim: for every f in C_c(R^(n+l)), integral_(eta_(x,r)(N_k)) f dH^n -> integral_(T_x N_k) f dH^n as r -> 0+.
 Write f = f^+ - f^- with f^+, f^- in C_c nonnegative, and treat f >= 0; all integrals below are finite. By (S), and by (AF)(ii) for G_k on the Borel set B_k (where G_k is injective with injective derivative):
 integral_(eta_(x,r)(N_k)) f dH^n = r^-n integral_(N_k) f((z - x)/r) dH^n(z) = r^-n integral_(B_k) f((G_k(v) - x)/r) JG_k(v) dv.
 The substitution v = u + r w (L^n(r E) = r^n L^n(E)) turns this into integral_((B_k - u)/r) f((G_k(u + r w) - G_k(u))/r) JG_k(u + r w) dw.
 Let f = 0 outside B_(R_f)(0). The integrand vanishes for |w| > R_f/c_k, as |G_k(u + r w) - G_k(u)| >= c_k r |w|, and it is bounded by sup|f| times sup over B_k of JG_k.
 For fixed w: u + r w lies in B_k for small r (B_k is open), (G_k(u + r w) - G_k(u))/r -> DG_k(u)w, and JG_k(u + r w) -> JG_k(u) (JG_k(v) = normDet(DG_k(v)) is continuous, by continuity of DG_k and SimonGMT Chapter02.continuous_normDet).
 Dominated convergence along r -> 0+ (the filter is countably generated) gives the limit integral_(R^n) f(DG_k(u)w) JG_k(u) dw. This equals integral_(T_x N_k) f dH^n by (AF)(ii) for the injective linear map DG_k(u) on s = R^n, whose Jacobian is the constant JG_k(u).
C2. x -> p_(T_x N_k) is continuous on N_k. Indeed:
 - u -> DG_k(u) is continuous;
 - for an injective linear map L : R^n -> R^(n+l), P_L := L (L^T L)^-1 L^T is self-adjoint and idempotent with range L(R^n), so it is the orthogonal projection onto L(R^n). It depends continuously on L on the open set of injective maps: L^T L is invertible there, and inversion is continuous on invertible operators (Mathlib NormedRing.inverse_continuousAt);
 - u = (G_k restricted to B_k)^-1(x) depends continuously on x in N_k, by B3.

Part D. Unweighted approximate tangent planes (proof of Simon 1.6 "=>"). Let C be a compact subset of M with H^n(C) < infinity, and C_k := C cap M'_k for k >= 1.
D1. Let x in C_k, and let f in C_c with f = 0 outside B_R(0). Write eta := eta_(x,r). Since eta is injective, C is the disjoint union of C_k and C minus C_k, and N_k is the disjoint union of C_k and N_k minus C_k, we have
 integral_(eta(C)) f = integral_(eta(N_k)) f - integral_(eta(N_k minus C_k)) f + integral_(eta(C minus C_k)) f.
 All integrals are finite, since H^n(eta(C)) = r^-n H^n(C) and H^n(eta(N_k)) = r^-n H^n(N_k) are finite and f is bounded.
D2. By (S), |integral_(eta(C minus C_k)) f| <= sup|f| r^-n H^n((C minus C_k) cap B_(rR)(x)). This tends to 0 for H^n-a.e. x in C_k, by (UD) with lambda := H^n restricted to C (finite) and A := C minus C_k (lambda-null-measurable, and x is not in A).
D3. Likewise |integral_(eta(N_k minus C_k)) f| <= sup|f| r^-n H^n((N_k minus C_k) cap B_(rR)(x)) -> 0 for H^n-a.e. x in C_k, by (UD) with lambda := H^n restricted to N_k (finite by B3) and A := N_k minus C_k.
D4. The exceptional null sets of D2 and D3 depend only on C, C_k and N_k, not on f or R: vanishing upper density at x means r^-n lambda(A cap B_(rR)(x)) -> 0 for every R > 0.
D5. With C1, for H^n-a.e. x in C_k we get integral_(eta_(x,r)(C)) f dH^n -> integral_(T_x N_k) f dH^n for all f in C_c simultaneously. Testing with f_eps and g_eps (Notation) and letting eps -> 0 gives r^-n H^n(C cap B_r(x)) -> omega_n (Simon Remark 1.5(3)). Here H^n(T cap B_s(0)) = omega_n s^n for every n-plane T (see Part F). In particular r^-n H^n(C cap B_(rR)(x)) stays bounded as r -> 0. Since H^n(M'_0) = 0, these conclusions hold for H^n-a.e. x in C, with plane T_x N_k for x in C_k.

Part E. Weighted approximate tangent planes (Simon Remark 1.8(1) and Theorem 1.9).
E1. Borel representative. By V.aemeasurable_mult, fix a Borel function theta~ with theta~ = theta at H^n-a.e. point of M, and a Borel H^n-null set N_theta containing {x in M : theta(x) != theta~(x)}.
 For m >= 1 let E_m := (M minus N_theta) cap closure(U_m) cap {theta~ >= 1/m}. It is H^n-null-measurable, and H^n(E_m) <= m integral_(M cap closure(U_m)) theta dH^n < infinity by (L). Also M minus N_theta is the union of the E_m, since theta = theta~ > 0 there and M is contained in U. Choose a Borel E'_m contained in E_m with H^n(E_m minus E'_m) = 0.
E2. Lusin compacts. For each m and i >= 1, apply (Lu) with the finite measure nu := H^n restricted to E'_m, A := E'_m, the Borel function theta~ and tau = 1/i. The hypothesis of (Lu) holds because finite measures on metric spaces are weakly regular (Mathlib instance MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure; nu(R^(n+l)) = H^n(E'_m) < infinity). This gives a closed C_(m,i) contained in E'_m with H^n(E'_m minus C_(m,i)) < 1/i and theta~ continuous on C_(m,i).
 C_(m,i) is compact (a closed subset of the compact set closure(U_m)), is contained in M and has finite H^n-measure. Since theta = theta~ on C_(m,i), the restriction of theta to C_(m,i) is continuous.
 Hence H^n(M minus the union over m, i of C_(m,i)) = 0. Enumerate the C_(m,i) as C_1, C_2, ....
E3. Fix j. For H^n-a.e. x in C_j, the following hold:
 (alpha) Part D applies to C = C_j at x, with plane T_x := T_x N_k, where k is such that x lies in M'_k.
 (beta) limsup_(r -> 0) r^-n mu((M minus C_j) cap B_r(x)) = 0. To see this, apply (UD), for each m' >= 1, to lambda := mu (its outer measure is Borel regular) and A := (M minus C_j) cap U_(m'). This A is mu-null-measurable and mu(A) <= mu(closure U_(m')) < infinity by (L). Every x in C_j lies in some U_(m') (C_j is a compact subset of U), and A cap B_r(x) = (M minus C_j) cap B_r(x) for small r.
 These exceptional sets do not depend on f.
E4. Let x be as in E3. Let f in C_c with f = 0 outside B_R(0), and let r be so small that B_(rR)(x) is contained in U. By (S):
 integral_(eta_(x,r)(M)) f(y) theta(x + r y) dH^n(y) = r^-n integral_(M minus C_j) f((z - x)/r) dmu(z) + r^-n integral_(C_j) f((z - x)/r) (theta(z) - theta(x)) dH^n(z) + theta(x) integral_(eta_(x,r)(C_j)) f dH^n.
 - The first term is at most sup|f| r^-n mu((M minus C_j) cap B_(rR)(x)), which tends to 0 by (beta).
 - The second term is at most sup|f| times sup{|theta(z) - theta(x)| : z in C_j cap B_(rR)(x)} times r^-n H^n(C_j cap B_(rR)(x)). This tends to 0, because theta restricted to C_j is continuous at x and the last factor is bounded (D5).
 - The third term tends to theta(x) integral_(T_x) f dH^n, by (alpha).
 Hence T_x, which has finrank n, is a weighted approximate tangent plane of (M, theta) at x.
E5. Let Good be the set of x in M at which a weighted approximate tangent plane exists.
 - By E2-E4 and H^n(N_theta) = 0, H^n(M minus Good) = 0. Hence mu(complement of Good) = 0, as mu is absolutely continuous with respect to H^n restricted to M and mu(complement of M) = 0.
 - At x in Good, theta(x) > 0, so the plane is unique (SimonGMT HasWeightedApproximateTangentSpaceAt.unique). Therefore p_x = V.tangentProj x is the orthogonal projection onto it, which has finrank n. This is the first half of (c).
 - Moreover, for H^n-a.e. x in M'_k (k >= 1) the weighted plane is T_x N_k, by E3-E4, because the C_j cover M up to an H^n-null set.

Part F. Density (Simon Remark 1.8(2)). Let x in Good with plane T, and 0 < eps < 1.
 Since g_eps <= indicator of B_1(0) <= f_eps and theta > 0 on M, (S) gives
 r^-n integral g_eps((z - x)/r) dmu(z) <= r^-n mu(B_r(x)) <= r^-n integral f_eps((z - x)/r) dmu(z).
 The outer terms are the weighted blow-up integrals of g_eps and f_eps. They converge to theta(x) integral_T g_eps dH^n >= theta(x) omega_n (1 - eps)^n and to theta(x) integral_T f_eps dH^n <= theta(x) omega_n (1 + eps)^n, respectively. Here H^n(T cap B_s(0)) = omega_n s^n for every n-plane T and s >= 0. To see this, push H^n on T forward along the subtype isometry T -> R^(n+l) (Mathlib Isometry.map_euclideanHausdorffMeasure); on the n-dimensional inner product space T, muHE[n] = volume (InnerProductSpace.euclideanHausdorffMeasure_eq_volume); and volume(closedBall 0 s) = ofReal(s)^n ofReal(sqrt(pi)^n/Gamma(n/2 + 1)) (InnerProductSpace.volume_closedBall), where sqrt(pi)^n = pi^(n/2).
 Letting eps -> 0 gives mu(B_r(x))/(omega_n r^n) -> theta(x) as r -> 0+. These quantities are finite for small r by (L), so in [0, infinity] this is V.HasDensity x (V.mult x). This is the second half of (c).

Part G. Measurability (a). Define Pi(x) := p_(T_x N_k) if x lies in N_k minus (N_0 union ... union N_(k-1)) for some k >= 1, and Pi(x) := 0 otherwise.
 - The pieces P_k := N_k minus (N_0 union ... union N_(k-1)) are pairwise disjoint Borel sets, and psi_k(x) := p_(T_x N_k) is continuous on N_k, which contains P_k (C2). So Pi is Borel measurable. For a Borel set S of linear maps, Pi^-1(S) is the union over k of (P_k cap psi_k^-1(S)), together with the complement of the union of the P_k if 0 is in S. Each P_k cap psi_k^-1(S) is Borel, because psi_k restricted to the Borel set P_k is continuous, hence Borel (equivalently, P_k.piecewise psi_k 0 is measurable by Mathlib ContinuousOn.measurable_piecewise). Pi takes values in the finite-dimensional normed space of linear maps of R^(n+l), so it is strongly measurable.
 - By E5, for mu-a.e. x there is k >= 1 with x in Good cap M'_k and p_x = p_(T_x N_k) = Pi(x). Here M'_k is contained in N_k minus (N_0 union ... union N_(k-1)), and mu(M'_0) = 0.
 Hence V.tangentProj = Pi mu-a.e., and V.tangentProj is mu-a.e. strongly measurable. This proves (a).

Part H. Integrability (b).
 - For every x, V.tangentProj x is 0 or an orthogonal projection, so its operator norm is at most 1; the same holds for p_T.
 - For a linear map A of R^(n+l), hsNormSq(A) = sum_(i < n+l) |A e_i|^2 <= (n + l) ||A||^2. So 0 <= hsNormSq(p_x - p_T) <= 4(n + l) for all x.
 - The map A -> hsNormSq(A - p_T) is continuous, so by (a) x -> hsNormSq(p_x - p_T) is mu-a.e. strongly measurable.
 - For compact K contained in U, mu(K) < infinity by (L).
 A bounded a.e.-strongly measurable function is integrable on a set of finite measure, which proves (b).

## Key steps

1. C^1 approximation, Part A: Rademacher; Borel remainder suprema Rsup_k computed on a countable dense set; Egorov and Lusin (partial derivatives) on the bounded shells S_m; closed locally finite union A with L^n(R^n minus A) < eps
2. Df is continuous on A (each K_m is a relative neighbourhood in A) and the Taylor remainders are uniform on compacts of A: these are the three fields of HasWhitneyC1Compatibility, so the checked Whitney theorem gives g in C^1 with g = f on A
3. Componentwise application with tolerances eps_j, sum_j eps_j < eps: L^n({F != G}) <= sum_j L^n(R^n minus A_j) < eps
4. C^1 cover: M lies in N_0 union countably many bi-Lipschitz C^1 images N_k = G_k(B_k) (Z_j null, critical images null, inverse-function estimate, Lindelof); disjoint null-measurable pieces M'_k
5. Blow-ups of N_k converge to T_x N_k (area formula, substitution, dominated convergence), and x -> p_(T_x N_k) is continuous on N_k
6. Upper density theorem: a compact C in M of finite H^n-measure has approximate tangent plane T_x N_k and density omega_n at H^n-a.e. x
7. Borel representative of theta, Lusin compacts on which theta is continuous, and the localized upper density theorem for mu: weighted approximate tangent planes exist H^n-a.e., hence mu-a.e., and are unique since theta > 0
8. Radial cut-offs squeezing the unit ball give mu(B_r(x))/(omega_n r^n) -> theta(x), i.e. HasDensity
9. tangentProj agrees mu-a.e. with the Borel map Pi, giving (a); a bounded integrand and finite mass on compacts give (b)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `diff GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean (identical)`
- `grep -n 'def C1Approximation|def WhitneyExtension|def Rademacher' GMT/Ch02/Contract.lean; grep -n sorry GMT/Ch02/Submission.lean`
- `grep -o 'lip_approx_[a-z_]*' dag.json DAG.md dag.mmd issue-workers.json problem.json (no matches)`
- `python3 -I: list dag.json nodes with 'tangent' in id (aal_tangent_structure, rectifiableVarifold_ae_tangentProj_starProjection)`
- `grep -n 'theorem LipschitzWith.ae_differentiableAt' <snapshot>/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `grep -n 'theorem tendstoUniformlyOn_of_ae_tendsto' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `grep -n 'theorem measurableSet_of_differentiableAt|theorem measurable_fderiv' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `grep -rn 'exists_isClosed_diff_lt' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem isClosed_iUnion' <snapshot>/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `grep -rn 'theorem contDiff_euclidean|theorem contDiff_piLp' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem norm_fderiv_le_of_lipschitz' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `grep -rn 'theorem ContinuousOn.measurable_piecewise' <snapshot>/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `grep -rn 'norm_image_sub_le_of_norm_fderiv_le' <snapshot>/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `grep -n 'theorem hausdorffMeasure_homothety_image' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n 'euclideanHausdorffMeasure_eq_volume|def MeasureTheory.Measure.euclideanHausdorffMeasure' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn sorry .lake/packages/simongmt/Poincare/SimonGMT (0 matches); git -C lake-packages-25730c7c/simongmt rev-parse HEAD`
- `grep -n '^theorem|^structure' SimonGMT/Chapter02/WhitneyExtension.lean SimonGMT/Chapter02/WhitneyJet.lean`
- `grep -n '^theorem' -A 12 SimonGMT/Chapter01/Lusin.lean`
- `grep -rn 'theorem simon_theorem_3_6' -A 30 SimonGMT/Chapter01/; grep -n 'def dimensionalDensityQuotient|def dimensionalUpperDensity' SimonGMT/Chapter01/Densities.lean`
- `grep -n 'theorem measure_toOuterMeasure_isBorelRegular' SimonGMT/Chapter01/Basic.lean; grep -n 'simonAreaNormalization' SimonGMT/Chapter02/AreaNormalization.lean`
- `grep -n '^theorem' SimonGMT/Chapter02/{AreaLipschitz,AreaCritical,AreaFormula,AreaNoninjective,Area}.lean; grep -rn 'theorem weighted_area_formula_volume_of_injective_derivative|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' SimonGMT/Chapter02`
- `grep -n '^theorem|^def' SimonGMT/Chapter03/{SubmanifoldCover,DisjointCover,Rectifiable}.lean`
- `sed -n 150,290p book/sources/chapter-02-source.txt (printed proof of Thm 1.5); sed -n 1,360p book/sources/chapter-03-source.txt (1.1-1.9)`
- `lean --root=/tmp/lipapprox-dec-v2 -o GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; lean -o LipApproxAux/WhitneyExtension.olean LipApproxAux/WhitneyExtension.lean (verbatim copy of SimonGMT Chapter02/WhitneyExtension.lean)`
- `lean --root=/tmp/lipapprox-dec-v2 c1a/Api.lean (#check of cited APIs and #print axioms for Whitney and Lusin)`
- `lean --root=/tmp/lipapprox-dec-v2 c1a/C1A.lean (C1ACheck.c1_approx_scalar, C1ACheck.c1_approx; #print axioms)`
- `python3 -I scripts/gen_checks.py decomposition statements (verifier/lean_contract.validate_lean_statement); lean check/lip_approx_*.lean; lean check/All.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-03-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-tangent-structure-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/lipapprox-dec-v2/c1a/C1A.lean`
- `/tmp/lipapprox-dec-v2/c1a/Api.lean`
- `/tmp/lipapprox-dec-v2/LipApproxAux/WhitneyExtension.lean`
- `/tmp/lipapprox-dec-v2/check/All.lean`

Pinned versions. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The pinned SimonGMT, 2b3663083f3fe399b6296fb8eaee52169170e197, lies outside the snapshot and contains no sorry. The workspace GMT/Ch05/Submission.lean is byte-identical to the snapshot copy.

C1A has no usable proof anywhere:
- GMT/Ch02/Contract.lean:199 defines C1Approximation, but GMT/Ch02/Submission.lean:377 proves its main_theorem by sorry.
- SimonGMT Chapter03/SubmanifoldCover.lean proves only the C^1-to-rectifiable direction of Lemma 1.2.
So the proof is supplied as Part A of tangent_structure.

Checked ingredients located in Mathlib (paths under mathlib/Mathlib):
- LipschitzWith.ae_differentiableAt (Analysis/Calculus/Rademacher.lean:385);
- measurableSet_of_differentiableAt and measurable_fderiv (Analysis/Calculus/FDeriv/Measurable.lean:372, 378);
- tendstoUniformlyOn_of_ae_tendsto (MeasureTheory/Function/Egorov.lean:205);
- MeasurableSet.exists_isClosed_sdiff_lt (MeasureTheory/Measure/Regular.lean, alias exists_isClosed_diff_lt at :1044);
- LocallyFinite.isClosed_iUnion (Topology/LocallyFinite.lean:128);
- contDiff_euclidean (Analysis/InnerProductSpace/Calculus.lean:339);
- norm_fderiv_le_of_lipschitz (Analysis/Calculus/FDeriv/Basic.lean:947);
- Convex.norm_image_sub_le_of_norm_fderiv_le (Analysis/Calculus/MeanValue.lean:499);
- ContinuousOn.measurable_piecewise (MeasureTheory/Constructions/BorelSpace/Basic.lean:523);
- hausdorffMeasure_homothety_image (MeasureTheory/Measure/Hausdorff.lean:1060);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187).

Checked ingredients located in SimonGMT (paths under Poincare/SimonGMT):
- Chapter02.exists_contDiff_one_extension_of_whitney (WhitneyExtension.lean:373); its hypothesis HasWhitneyC1Compatibility (WhitneyJet.lean:34) has the fields continuous_value, continuous_derivative and remainder;
- Chapter01.exists_isClosed_continuousOn_of_measurable, the finite-measure Lusin theorem (Lusin.lean:127);
- Chapter01.simon_theorem_3_6 (DensityComparison.lean:332), with its density quotient over closed balls (Densities.lean);
- Chapter01.measure_toOuterMeasure_isBorelRegular (Basic.lean:309);
- simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure and simonAreaNormalization_pos/_ne_top (Chapter02/AreaNormalization.lean:45, 31, 37);
- Chapter02.area_image_criticalSet_eq_zero (AreaCritical.lean:185);
- Chapter02.weighted_area_formula_volume_of_injective_derivative (WeightedArea.lean:120);
- Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (Lipschitz.lean:216);
- Chapter03.simon_remark_1_3_nullMeasurable (DisjointCover.lean:109);
- Chapter03.HasWeightedApproximateTangentSpaceAt.unique (Rectifiable.lean:345).
None of these is the Chapter04.RectifiableVarifold that the chapter README excludes.

The book's printed proofs are followed: Thm 1.5 at book/sources/chapter-02-source.txt lines 165-270, and Ch. 3, 1.1-1.9.

Lean results:
- /tmp/lipapprox-dec-v2/c1a/C1A.lean compiles with 0 errors and no sorry.
- C1ACheck.c1_approx_scalar, C1ACheck.c1_approx, exists_contDiff_one_extension_of_whitney and exists_isClosed_continuousOn_of_measurable depend only on propext, Classical.choice and Quot.sound.
- All 11 child types elaborate in the contract scope with 0 errors and only sorry warnings, and pass validate_lean_statement.

No lip_approx_ name is reserved anywhere in the DAG. The tangent nodes of other branches, aal_tangent_structure and rectifiableVarifold_ae_tangentProj_starProjection, have different Lean types, so there is no collision and no reuse.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
