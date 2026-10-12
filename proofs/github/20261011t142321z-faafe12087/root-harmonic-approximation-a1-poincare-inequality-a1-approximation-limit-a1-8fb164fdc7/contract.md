<!-- theorem-id: gmt-ch05/root.harmonic_approximation-a1.poincare_inequality-a1.approximation_limit-a1 -->

## Theorem `Submission.poincare_approx_ball_double_integral_bound`

Let n ∈ ℕ, 0 < r ≤ 1, f : ℝ^n → ℝ and g : ℝ^n → ℝ^n be a.e.-strongly measurable for Lebesgue measure restricted to B_r = ball(0, r), and let φ_j : ℝ^n → ℝ (j ∈ ℕ) be C^1 functions such that ∫⁻_{B_r} ‖φ_j − f‖ₑ² → 0 and ∫⁻_{B_r} ‖∇φ_j − g‖ₑ² → 0 as j → ∞. Then ∫⁻_{x ∈ B_r} ∫⁻_{y ∈ B_r} ‖f(x) − f(y)‖ₑ² dy dx ≤ 2^{n+2} · |B_1| · ∫⁻_{B_r} ‖g‖ₑ², where |B_1| is the Lebesgue measure of the open unit ball (lintegrals in [0, ∞]).

Node: `root.harmonic_approximation-a1.poincare_inequality-a1.approximation_limit-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/406

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1042

Decomposition children: None

## Lean problem

Declaration: `Submission.poincare_approx_ball_double_integral_bound`

```lean
∀ (n : ℕ) (f : Rn n → ℝ) (g : Rn n → Rn n) (φ : ℕ → Rn n → ℝ) (r : ℝ), 0 < r → r ≤ 1 → AEStronglyMeasurable f (volume.restrict (ball (0 : Rn n) r)) → AEStronglyMeasurable g (volume.restrict (ball (0 : Rn n) r)) → (∀ j, ContDiff ℝ 1 (φ j)) → Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖φ j x - f x‖ₑ ^ 2) atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖gradient (φ j) x - g x‖ₑ ^ 2) atTop (𝓝 0) → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖f x - f y‖ₑ ^ 2 ≤ (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) * ∫⁻ x in ball (0 : Rn n) r, ‖g x‖ₑ ^ 2
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

- Parent DAG node: `root.harmonic_approximation-a1.poincare_inequality-a1`
- Child DAG node: `root.harmonic_approximation-a1.poincare_inequality-a1.approximation_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 2 of the parent proof ('Passage to f on B_r': Minkowski, an a.e.-convergent subsequence, Fatou first in y and then in x), stated for an arbitrary approximating sequence of the form produced by the uncle lemma Submission.w12_ball_smooth_approximation, so that this lemma itself only needs the sibling (3) Submission.poincare_c1_ball_double_integral_bound (key smooth_estimate). The measurability hypothesis on g is essential (lintegrals of non-measurable functions are lower integrals).

Notation. B := B_r; μ := Lebesgue measure restricted to B (a finite measure); C := 2^{n+2}|B_1|, which is finite since |B_1| < ∞; ‖u‖_2 := eLpNorm u 2 μ. For a.e.-strongly measurable u, ‖u‖_2 = (∫‖u‖ₑ² dμ)^{1/2} (eLpNorm_eq_lintegral_rpow_enorm_toReal), hence ‖u‖_2² = ∫‖u‖ₑ² dμ, and if ∫‖u_j‖ₑ² dμ → 0 then ‖u_j‖_2 → 0 (continuity of a ↦ a^{1/2} on [0, ∞] and 0^{1/2} = 0).

Proof.
0. Representative. Let f' be strongly measurable with f = f' μ-a.e. (AEStronglyMeasurable.mk). Then ∫_B∫_B ‖f(x) − f(y)‖ₑ² = ∫_B∫_B ‖f'(x) − f'(y)‖ₑ²: for each x the inner integrands agree μ-a.e. in y, and then the outer integrands agree μ-a.e. in x (lintegral_congr_ae twice). Likewise ∫_B ‖φ_j − f'‖ₑ² = ∫_B ‖φ_j − f‖ₑ² → 0. So it suffices to prove the claim for f'.
1. Regularity. Each φ_j is continuous and ∇φ_j = toDual⁻¹ ∘ Dφ_j is continuous (φ_j is C^1).
2. A.e.-convergent subsequence. ‖φ_j − f'‖_2 → 0, hence φ_j → f' in μ-measure (tendstoInMeasure_of_tendsto_eLpNorm with p = 2 ≠ 0), and there is a strictly increasing ns : ℕ → ℕ with φ_{ns(i)}(x) → f'(x) for μ-a.e. x (TendstoInMeasure.exists_seq_tendsto_ae).
3. Inner Fatou. Fix x at which the convergence of step 2 holds (this is μ-a.e. x). For μ-a.e. y the convergence holds at y too; by continuity of (a, b) ↦ ‖a − b‖ₑ² : ℝ × ℝ → [0, ∞], ‖φ_{ns i}(x) − φ_{ns i}(y)‖ₑ² → ‖f'(x) − f'(y)‖ₑ², so ‖f'(x) − f'(y)‖ₑ² = liminf_i ‖φ_{ns i}(x) − φ_{ns i}(y)‖ₑ² (Tendsto.liminf_eq). By lintegral_congr_ae and Fatou's lemma (lintegral_liminf_le; each y ↦ ‖φ_{ns i}(x) − φ_{ns i}(y)‖ₑ² is measurable): ∫_B ‖f'(x) − f'(y)‖ₑ² dy ≤ liminf_i G_i(x), where G_i(x) := ∫_B ‖φ_{ns i}(x) − φ_{ns i}(y)‖ₑ² dy.
4. Outer Fatou. Each G_i is measurable (Measurable.lintegral_prod_right', the integrand being measurable on ℝ^n × ℝ^n). By step 3 (μ-a.e. in x; lintegral_mono_ae) and Fatou again: ∫_B∫_B ‖f'(x) − f'(y)‖ₑ² ≤ ∫_B liminf_i G_i ≤ liminf_i ∫_B G_i = liminf_i D_i, with D_i := ∫_B∫_B ‖φ_{ns i}(x) − φ_{ns i}(y)‖ₑ² dy dx.
5. Smooth estimate and Minkowski. By sibling (3) (φ_{ns i} is C^1 and 0 < r ≤ 1): D_i ≤ C ∫_B ‖∇φ_{ns i}‖ₑ² = C ‖∇φ_{ns i}‖_2². Writing ∇φ_{ns i} = g + (∇φ_{ns i} − g), Minkowski's inequality in L²(μ) (eLpNorm_add_le, 1 ≤ 2) gives ‖∇φ_{ns i}‖_2 ≤ ‖g‖_2 + ε_i with ε_i := ‖∇φ_{ns i} − g‖_2. Hence D_i ≤ C (‖g‖_2 + ε_i)².
6. Limit. Since ∇φ_j − g is a.e.-strongly measurable and ∫_B ‖∇φ_j − g‖ₑ² → 0, we get ‖∇φ_j − g‖_2 → 0, so ε_i → 0 (composition with ns, which tends to ∞; StrictMono.tendsto_atTop). By continuity of addition and squaring on [0, ∞] and of multiplication by the finite constant C (ENNReal.Tendsto.const_mul), C(‖g‖_2 + ε_i)² → C‖g‖_2².
7. Conclusion. ∫_B∫_B ‖f'(x) − f'(y)‖ₑ² ≤ liminf_i D_i ≤ liminf_i C(‖g‖_2 + ε_i)² (liminf_le_liminf) = C‖g‖_2² (Tendsto.liminf_eq) = C ∫_B ‖g‖ₑ² = 2^{n+2} |B_1| ∫_{B_r} ‖g‖ₑ². All steps are valid in [0, ∞], including the case ∫_{B_r} ‖g‖ₑ² = ∞. ∎

Appendix: verified Lean proof. The following text was compiled on 2026-10-11 against the frozen contract (lean4 v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d) inside namespace GMT.Ch05.Submission, with the sibling theorem poincare_c1_ball_double_integral_bound declared earlier (its frozen statement) and no other Submission declarations; #print axioms reports only propext, Classical.choice, Quot.sound once the sibling is proved.
```lean
theorem poincare_approx_ball_double_integral_bound : ∀ (n : ℕ) (f : Rn n → ℝ) (g : Rn n → Rn n) (φ : ℕ → Rn n → ℝ) (r : ℝ), 0 < r → r ≤ 1 → AEStronglyMeasurable f (volume.restrict (ball (0 : Rn n) r)) → AEStronglyMeasurable g (volume.restrict (ball (0 : Rn n) r)) → (∀ j, ContDiff ℝ 1 (φ j)) → Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖φ j x - f x‖ₑ ^ 2) atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖gradient (φ j) x - g x‖ₑ ^ 2) atTop (𝓝 0) → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖f x - f y‖ₑ ^ 2 ≤ (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) * ∫⁻ x in ball (0 : Rn n) r, ‖g x‖ₑ ^ 2 := by
  intro n f g φ r hr0 hr1 hf hg hφ h1 h2
  set B := ball (0 : Rn n) r with hB
  set μ : Measure (Rn n) := volume.restrict B with hμ
  set C : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) with hC
  have hCtop : C ≠ ∞ := ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne
  -- L² bookkeeping: eLpNorm u 2 μ = (∫ ‖u‖ₑ²)^{1/2}
  have eL2 : ∀ {E : Type} [NormedAddCommGroup E] {u : Rn n → E}, AEStronglyMeasurable u μ →
      eLpNorm u 2 μ = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    intro E _ u hu
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hu]
    simp
  have eL2sq : ∀ {E : Type} [NormedAddCommGroup E] {u : Rn n → E}, AEStronglyMeasurable u μ →
      eLpNorm u 2 μ ^ 2 = ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ := by
    intro E _ u hu
    rw [eL2 hu, ← ENNReal.rpow_mul_natCast]
    norm_num
  have tL2 : ∀ {E : Type} [NormedAddCommGroup E] {u : ℕ → Rn n → E},
      (∀ j, AEStronglyMeasurable (u j) μ) → Tendsto (fun j => ∫⁻ x, ‖u j x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) →
      Tendsto (fun j => eLpNorm (u j) 2 μ) atTop (𝓝 0) := by
    intro E _ u hu h
    simp_rw [eL2 (hu _)]
    have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  -- 0. replace f by a strongly measurable representative (both sides unchanged)
  have hff' := hf.ae_eq_mk
  have hfm : StronglyMeasurable (hf.mk f) := hf.stronglyMeasurable_mk
  set f' := hf.mk f
  have hdbl : ∫⁻ x in B, ∫⁻ y in B, ‖f x - f y‖ₑ ^ 2 = ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2 := by
    have hin : ∀ x, ∫⁻ y in B, ‖f x - f y‖ₑ ^ 2 = ∫⁻ y in B, ‖f x - f' y‖ₑ ^ 2 := fun x =>
      lintegral_congr_ae (hff'.mono fun y hy => by simp [hy])
    simp_rw [hin]
    exact lintegral_congr_ae (hff'.mono fun x hx => by simp [hx])
  rw [hdbl]
  have h1' : Tendsto (fun j => ∫⁻ x in B, ‖φ j x - f' x‖ₑ ^ 2) atTop (𝓝 0) := by
    refine h1.congr fun j => ?_
    exact lintegral_congr_ae (hff'.mono fun x hx => by simp only [hx])
  have hφc : ∀ j, Continuous (φ j) := fun j => (hφ j).continuous
  have hgc : ∀ j, Continuous (gradient (φ j)) := fun j =>
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp ((hφ j).continuous_fderiv one_ne_zero)
  -- 1. an a.e.-convergent subsequence
  have hconv : Tendsto (fun j => eLpNorm (φ j - f') 2 μ) atTop (𝓝 0) :=
    tL2 (fun j => (hφc j).aestronglyMeasurable.sub hfm.aestronglyMeasurable) h1'
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hconv).exists_seq_tendsto_ae
  -- 2. Fatou, first in y then in x
  have hsqc : Continuous (fun p : ℝ × ℝ => ‖p.1 - p.2‖ₑ ^ 2) :=
    (ENNReal.continuous_pow 2).comp (continuous_enorm.comp (continuous_fst.sub continuous_snd))
  have hFatou : ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2 ≤
      liminf (fun i => ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := by
    have hpt : ∀ᵐ x ∂μ, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2 ≤
        liminf (fun i => ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := by
      filter_upwards [hae] with x hx
      calc ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2
          = ∫⁻ y in B, liminf (fun i => ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := by
            refine lintegral_congr_ae ?_
            filter_upwards [hae] with y hy
            exact (((hsqc.tendsto _).comp (hx.prodMk_nhds hy)).liminf_eq).symm
        _ ≤ liminf (fun i => ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop :=
            lintegral_liminf_le fun i =>
              ((measurable_const.sub (hφc _).measurable).enorm.pow_const 2)
    calc ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2
        ≤ ∫⁻ x in B, liminf (fun i => ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop :=
          lintegral_mono_ae hpt
      _ ≤ liminf (fun i => ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop :=
          lintegral_liminf_le fun i =>
            ((((hφc _).measurable.comp measurable_fst).sub
              ((hφc _).measurable.comp measurable_snd)).enorm.pow_const 2).lintegral_prod_right'
  -- 3. the smooth estimate (sibling) plus Minkowski in L²(B_r)
  have hbound : ∀ i, ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2 ≤
      C * (eLpNorm g 2 μ + eLpNorm (gradient (φ (ns i)) - g) 2 μ) ^ 2 := by
    intro i
    refine (poincare_c1_ball_double_integral_bound n (φ (ns i)) (hφ _) r hr0 hr1).trans ?_
    gcongr
    rw [← eL2sq (hgc _).aestronglyMeasurable]
    gcongr
    calc eLpNorm (gradient (φ (ns i))) 2 μ
        = eLpNorm (g + (gradient (φ (ns i)) - g)) 2 μ := by rw [add_sub_cancel]
      _ ≤ _ := eLpNorm_add_le one_le_two
  have hε : Tendsto (fun j => eLpNorm (gradient (φ j) - g) 2 μ) atTop (𝓝 0) :=
    tL2 (fun j => (hgc j).aestronglyMeasurable.sub hg) h2
  have hlim : Tendsto (fun i => C * (eLpNorm g 2 μ + eLpNorm (gradient (φ (ns i)) - g) 2 μ) ^ 2)
      atTop (𝓝 (C * (eLpNorm g 2 μ + 0) ^ 2)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr hCtop)
    exact ((ENNReal.continuous_pow 2).tendsto _).comp
      (tendsto_const_nhds.add (hε.comp hns.tendsto_atTop))
  -- 4. conclusion
  calc ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2
      ≤ liminf (fun i => ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := hFatou
    _ ≤ liminf (fun i => C * (eLpNorm g 2 μ + eLpNorm (gradient (φ (ns i)) - g) 2 μ) ^ 2) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = C * (eLpNorm g 2 μ + 0) ^ 2 := hlim.liminf_eq
    _ = C * ∫⁻ x in B, ‖g x‖ₑ ^ 2 := by rw [add_zero, eL2sq hg]
```

## Key steps

1. Replace f by a strongly measurable a.e.-representative; both sides and the hypothesis are unchanged
2. L² convergence φ_j → f on B_r gives convergence in measure and an a.e.-convergent subsequence φ_{ns i}
3. Inner Fatou in y for a.e. x, using continuity of (a, b) ↦ ‖a − b‖ₑ²
4. Outer Fatou in x (inner integrals measurable via Measurable.lintegral_prod_right')
5. Sibling smooth_estimate for each φ_{ns i} plus Minkowski: D_i ≤ C(‖g‖_2 + ‖∇φ_{ns i} − g‖_2)²
6. The right side converges to C‖g‖_2² = C ∫_{B_r} ‖g‖ₑ²; conclude with liminf_le_liminf and Tendsto.liminf_eq

## Reference use

### local-project

Queries:
- `rg -n "theorem (lintegral_comp_smul|setLIntegral_comp_smul|lintegral_comp_mul_left|lintegral_comp_inv_smul|map_addHaar_smul|lintegral_comp_smul_of_pos|setLIntegral_comp_smul_of_pos|integral_comp_smul|setIntegral_comp_smul_of_pos|lintegral_add_right_eq_self|lintegral_add_left_eq_self|lintegral_sub_right_eq_self)" <snapshot>/mathlib/Mathlib`
- `rg -n "lintegral_comp_smul|lintegral_comp_mul|lintegral_add_right_eq_self|lintegral_add_left_eq_self|lintegral_sub_right_eq_self|lintegral_map_equiv|addHaar_smul\b|addHaar_preimage_smul|lintegral_smul_measure" <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `rg -n "theorem (lintegral_iUnion_of_directed|setLIntegral_iUnion_of_directed|tendsto_setLIntegral_of_monotone|lintegral_iSup_directed|lintegral_liminf_le|lintegral_iSup\b|lintegral_iSup'|tendstoInMeasure_of_tendsto_eLpNorm|exists_seq_tendsto_ae\b|eLpNorm_add_le|enorm_integral_le_lintegral_enorm|lintegral_mul_le_Lp_mul_Lq|setAverage_eq|lintegral_lintegral_swap|eLpNorm_eq_lintegral_rpow_enorm|integral_eq_sub_of_hasDerivAt|setLIntegral_measure_zero|lintegral_const_mul'|lintegral_prod_right'|Measure.restrict_iUnion_apply_eq_iSup|restrict_iUnion_le)" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem (Measurable\.lintegral_prod_right'|ContDiff\.continuous_fderiv|toDual_symm_apply|lintegral_map|volume_Icc|MemLp\.integrable|eLpNorm_eq_lintegral_rpow_enorm|measure_ball_lt_top|measure_ball_pos|lintegral_add_left_eq_self|lintegral_mono_set|ofReal_toReal|ae_restrict_of_ae_restrict_of_subset|AEStronglyMeasurable\.mono_set|hasGradientAt_iff_hasFDerivAt|gradient_eq|lintegral_indicator|setLIntegral_le_lintegral)\b" <snapshot>/mathlib/Mathlib`
- `rg -n "lintegral_prod_right'|theorem eLpNorm_eq_lintegral_rpow|theorem eLpNorm_eq_eLpNorm'|theorem lintegral_rpow_enorm_eq_rpow_eLpNorm'|theorem lintegral_lintegral_swap|theorem prod_restrict|theorem restrict_prod_eq_prod_univ" <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -l -i "poincar" <snapshot>/mathlib/Mathlib; rg -n -i "poincare_inequality|poincaré inequality|poincare inequality" <snapshot>/mathlib/Mathlib; rg -n -i "poincar" <snapshot>/project/GMT/Ch05/*.lean`
- `sed -n 330,370p <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean; sed -n 40,75p <snapshot>/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean; sed -n 660,690p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean; sed -n 210,245p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean; sed -n 265,300p and 445,470p <snapshot>/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean; sed -n 400,412p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `head -n 460 GMT/Ch05/Contract.lean | cmp - <check prefix>; sha256sum GMT/Ch05/Contract.lean; python3 listing of lean_name fields in runs/20261011T142321Z-faafe12087/dag.json and nodes/root-harmonic-approximation-a1/decomposition-v1.json`
- `grep -rl <each proposed lean_name> .humanize ../.swarm-worktrees/*/gmt-ch05/GMT (collision check: 0 hits each)`
- `lake env lean /tmp/poincare-decomp-check-7c1/Check.lean (frozen contract + sibling (A) and six child types as sorry + sorry-free parent assembly)`
- `lake env lean /tmp/poincare-review-9q2/Full.lean; lake env lean /tmp/poincare-decomp-check-7c1/iso/T1.lean ... T6.lean (each child alone, declared siblings stubbed); lake env lean /tmp/poincare-decomp-check-7c1/iso/TAll.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-poincare-inequality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/tmp/poincare-decomp-check-7c1/Check.lean`
- `/tmp/poincare-review-9q2/Full.lean`
- `/tmp/poincare-decomp-check-7c1/iso/TAll.lean`

Pinned snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The workspace and snapshot GMT/Ch05/Contract.lean are identical (sha256 c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12). The Lean checks reuse its first 460 lines byte-for-byte, with declarations placed in namespace GMT.Ch05.Submission.

No usable match: Mathlib has no Sobolev or W^{1,p} Poincaré inequality. rg -i 'poincar' finds only CurveIntegral/Poincare.lean (Poincaré lemma for curve integrals), Geometry/Manifold/PoincareConjecture.lean, UpperHalfPlane/Metric.lean, Dynamics/Ergodic/Conservative.lean and Lie/ring-theory files. 'Poincare' in the project is just the SimonGMT package namespace. The parent's own reference audit already showed no W^{1,2} Poincaré in simongmt; Chapter04/Poincare.lean is a varifold Poincaré-type inequality, a different statement. So the inequality must be built from the lemmas below.

Usable Mathlib API, all confirmed to exist and used in the verified child proofs:
- Change of variables and translation: Measure.map_addHaar_smul (Lebesgue/EqHaar.lean:336); lintegral_map (Integral/Lebesgue/Map.lean:27); lintegral_add_left_eq_self (to_additive of lintegral_mul_left_eq_self, Group/LIntegral.lean); finrank_euclideanSpace_fin.
- Directed unions and Fatou: setLIntegral_iUnion_of_directed (Integral/Lebesgue/Basic.lean:668), which needs no measurability; lintegral_iSup (Add.lean:36); lintegral_liminf_le (Add.lean:233); lintegral_const_mul' (Add.lean:420).
- Convergence in measure: tendstoInMeasure_of_tendsto_eLpNorm (ConvergenceInMeasure.lean:452), which in this version needs no measurability hypotheses; TendstoInMeasure.exists_seq_tendsto_ae (ConvergenceInMeasure.lean:273).
- Lp norms: eLpNorm_add_le (TriangleInequality.lean:54); eLpNorm_le_eLpNorm_mul_rpow_measure_univ and eLpNorm_eq_lintegral_rpow_enorm_toReal.
- Integrals and averages: enorm_integral_le_lintegral_enorm (Bochner/Basic.lean:333); setAverage_eq (Average.lean:402); MemLp.integrable (L1Space/Integrable.lean:657).
- Products: lintegral_lintegral_swap (Measure/Prod.lean:1071); Measurable.lintegral_prod_right' (Measure/Prod.lean:123).
- Calculus: intervalIntegral.integral_eq_sub_of_hasDerivAt (FundThmCalculus.lean:1148); ContDiff.continuous_fderiv (ContDiff/Defs.lean:1271); InnerProductSpace.toDual (Dual.lean); gradient (Gradient/Basic.lean).
- Balls and sets: Real.volume_Icc; measure_ball_pos; measure_ball_lt_top; ae_restrict_of_ae_restrict_of_subset.

Sibling (A) w12_ball_smooth_approximation has its frozen type taken from nodes/root-harmonic-approximation-a1/decomposition-v1.json. It is used only by the parent assembly. No proposed lean_name occurs in dag.json, any node JSON, or any swarm worktree.

Lean results:
(1) Check.lean (frozen contract, (A) and the six child types as sorry, sorry-free parent assembly) compiles. The only warnings are the seven expected 'declaration uses sorry'; there is none for w12_ball_poincare_inequality.
(2) Full proofs of all six children were written by an independent reviewer (Full.lean) and re-verified by me. Each child compiles in isolation with only its declared sibling dependencies stubbed (iso/T1–T6). The combined iso/TAll.lean compiles, and #print axioms gives [propext, Classical.choice, Quot.sound] for every child; the parent picks up sorryAx only through (A).

Public mathematical sources (textbook-level, cited in the child proofs): Gilbarg–Trudinger, Elliptic PDE of Second Order, Lemma 7.16 and (7.45) (Poincaré on convex domains, as cited by the parent); Evans, PDE, §5.8.1.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
