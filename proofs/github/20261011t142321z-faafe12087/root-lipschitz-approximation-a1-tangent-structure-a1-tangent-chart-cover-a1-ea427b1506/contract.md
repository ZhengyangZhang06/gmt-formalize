<!-- theorem-id: gmt-ch05/root.lipschitz_approximation-a1.tangent_structure-a1.tangent_chart_cover-a1 -->

## Theorem `Submission.lipts_rectifiable_tangent_chart_cover`

Let n >= 1 and l be natural numbers, R^m := EuclideanSpace R (Fin m), R^(n+l) = Amb n l, and H^n := muHE[n] on R^(n+l). Let M be a subset of R^(n+l) that is countably n-rectifiable in the sense of SimonGMT Chapter03.CountablyRectifiable n M: there are M_0 with H^n(M_0) = 0 and maps F_j : R^n -> R^(n+l) (j in N), each Lipschitz, with M contained in M_0 union the union over j of F_j(R^n). No measurability of M is assumed. Then there are sets N_k in R^(n+l) and maps T_k from R^(n+l) to the linear subspaces of R^(n+l) (k in N) such that, for every k:
 (i) N_k is Borel measurable;
 (ii) H^n(N_k) < infinity;
 (iii) x -> (T_k x).starProjection, the orthogonal projection onto T_k(x), is continuous on N_k for the operator-norm topology;
 (iv) for every x in N_k, T_k(x) is an approximate tangent space of N_k at x in the sense of SimonGMT Chapter03.HasApproximateTangentSpaceAt n N_k x (T_k x). That is, finrank T_k(x) = n and, for every continuous compactly supported f : R^(n+l) -> R, the integral of f over blowUpMap x r '' N_k tends to the integral of f over T_k(x), both with respect to H^n, as r -> 0+. Here blowUpMap x r z = r^-1 (z - x).
Moreover:
 (v) H^n(M minus the union over k of N_k) = 0.

Node: `root.lipschitz_approximation-a1.tangent_structure-a1.tangent_chart_cover-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/692

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/796

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/784, https://github.com/ZhengyangZhang06/gmt-formalize/issues/788, https://github.com/ZhengyangZhang06/gmt-formalize/issues/937

## Lean problem

Declaration: `Submission.lipts_rectifiable_tangent_chart_cover`

```lean
∀ (n ℓ : ℕ), 1 ≤ n → ∀ (M : Set (Amb n ℓ)), Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ (N : ℕ → Set (Amb n ℓ)) (T : ℕ → Amb n ℓ → Submodule ℝ (Amb n ℓ)), (∀ k, MeasurableSet (N k)) ∧ (∀ k, (μHE[n] : Measure (Amb n ℓ)) (N k) < ⊤) ∧ (∀ k, ContinuousOn (fun x => (T k x).starProjection) (N k)) ∧ (∀ k, ∀ x ∈ N k, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (N k) x (T k x)) ∧ (μHE[n] : Measure (Amb n ℓ)) (M \ ⋃ k, N k) = 0
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

- Parent DAG node: `root.lipschitz_approximation-a1.tangent_structure-a1`
- Child DAG node: `root.lipschitz_approximation-a1.tangent_structure-a1.tangent_chart_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 2, Theorem 1.5 (C^1 Approximation Theorem) and its printed proof (Rademacher 1.4, Lusin, Egoroff, closed subset, Whitney extension theorem 1.6); Simon Ch. 3, Lemma 1.2 ("only if") and Remark 1.3; and the blow-up computation for a C^1 piece in the proof of Ch. 3, Theorem 1.6 ("=>"). This is Parts A, B and C of the parent proof of root.lipschitz_approximation-a1.tangent_structure-a1 (fact F1). Part A is copied verbatim. Parts B and C are copied with five changes:
 (1) the input is the given Lipschitz cover of an arbitrary countably n-rectifiable M, instead of V.countablyRectifiable; no measurability of M is used;
 (2) neither the Borel hull N_0 nor the disjoint pieces M'_k of the parent's B3/B4 are needed, since conclusion (v) only needs an H^n-null superset of the uncovered part;
 (3) the charts are indexed by k in N;
 (4) the tangent field T_k and the checks of (i)-(v) are written out (C0, C1(a)-(e), C2 and Part D);
 (5) the linear-algebra half of the parent's C2 (for injective L, P_L = L (L^T L)^-1 L^T is the orthogonal projection onto L(R^n) and depends continuously on L) is the sibling projection_continuity, the reused comparator-accepted declaration Submission.aetp_starProjection_range_continuousOn; C2 below applies it.

Notation. H^n := muHE[n] on every Euclidean space. On R^n = EuclideanSpace R (Fin n), H^n equals Lebesgue measure L^n = volume (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume; InnerProductSpace.euclideanHausdorffMeasure_eq_volume). R^(n+l) = Amb n l = EuclideanSpace R (Fin (n+l)), and R^N := EuclideanSpace R (Fin N). B_r(x) is the closed ball and B^o_r(x) the open ball. eta_(x,r)(z) := r^-1 (z - x) is SimonGMT blowUpMap x r. For a subspace T, p_T := T.starProjection. For a map f, Df(x) := fderiv R f x (Mathlib's Frechet derivative, 0 where f is not differentiable). For a map G : R^n -> R^(n+l), JG(v) := areaJacobianAt G v = normDet(DG(v)) = (det(DG(v)^T DG(v)))^(1/2) (SimonGMT Chapter02.areaJacobianAt_eq_normDet). C_c is the space of continuous, compactly supported f : R^(n+l) -> R.

Checked tools. These come from the pinned Mathlib and the pinned SimonGMT. All are sorry-free and use only the axioms propext, Classical.choice and Quot.sound.
(Rad) Rademacher. A Lipschitz map between finite-dimensional real spaces is differentiable L^n-a.e. (Mathlib LipschitzWith.ae_differentiableAt). For any map f, the differentiability set is Borel, and x -> Df(x) and x -> Df(x)v are Borel (Mathlib measurableSet_of_differentiableAt, measurable_fderiv, measurable_fderiv_apply_const). If f is Lambda-Lipschitz, then ||Df(x)|| <= Lambda (Mathlib norm_fderiv_le_of_lipschitz).
(Eg) Egorov (Mathlib tendstoUniformlyOn_of_ae_tendsto). Let S be a measurable set of finite measure and h_k strongly measurable real functions with h_k -> h at every point of S. For every tau > 0 there is a measurable t contained in S with measure <= tau such that h_k -> h uniformly on S minus t.
(Lu) Lusin (SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable). Let nu be a measure on R^d such that every measurable set S with nu(S) < infinity contains, for every tau > 0, a closed F with nu(S minus F) < tau. If A is measurable with nu(A) < infinity, h : R^d -> R is Borel and tau > 0, then there is a closed C contained in A with nu(A minus C) < tau and h restricted to C continuous. Here only nu = L^n is used; its hypothesis holds because Lebesgue measure is weakly regular (Mathlib MeasurableSet.exists_isClosed_diff_lt).
(Wh) Whitney (SimonGMT Chapter02.exists_contDiff_one_extension_of_whitney). Let A be a closed subset of R^n, h : R^n -> R and D : R^n -> (R^n ->L[R] R) with HasWhitneyC1Compatibility A h D, i.e.
 (W1) ContinuousOn h A;
 (W2) ContinuousOn D A;
 (W3) for every compact K contained in A and every tau > 0 there is delta > 0 with |h(y) - h(x) - D(x)(y - x)| <= tau |y - x| whenever x in K, y in A and |x - y| < delta.
 Then there is g : R^n -> R with ContDiff R 1 g, g = h on A, and HasFDerivAt g (D a) a for every a in A.
(S) Scaling. eta_(x,r) is a similarity with ratio 1/r, so H^n(eta_(x,r)(E)) = r^-n H^n(E) (Mathlib hausdorffMeasure_homothety_image and isometry invariance). Equivalently, the image of H^n restricted to E under eta_(x,r) is r^n times H^n restricted to eta_(x,r)(E). Hence integral_(eta_(x,r)(E)) h dH^n = r^-n integral_E h((z - x)/r) dH^n(z) for H^n-measurable E and measurable h >= 0. For signed h, h is integrable on eta_(x,r)(E) iff z -> h((z - x)/r) is integrable on E, and then the same identity holds.
(AF) Area formula (SimonGMT Chapter02).
 (i) For every map G : R^n -> R^N, H^n(G({v : G is differentiable at v and DG(v) is not injective})) = 0 (area_image_criticalSet_eq_zero, AreaCritical.lean:185).
 (ii) Let s be a Borel subset of R^n, and let G be differentiable at every point of s, with injective derivative there, and injective on s. Then integral_(G(s)) h dH^n = integral_s JG(v) h(G(v)) dv for every Borel h : R^(n+l) -> [0, infinity] (weighted_area_formula_volume_of_injective_derivative, WeightedArea.lean:120; a lintegral identity with ofReal(JG)).
 (iii) A K-Lipschitz map on a set A multiplies H^n(A) by at most K^n (euclideanHausdorffMeasure_image_le_of_lipschitzOn, Lipschitz.lean:216). In particular, Lipschitz maps send L^n-null sets to H^n-null sets.
(LinA) Linear area formula (SimonGMT Chapter02.weighted_linear_area_formula, AreaLinearWeighted.lean:51). For an injective linear map L : R^n -> R^(n+l), a Borel set A in R^n and g : R^(n+l) -> [0, infinity], integral_(L(A)) g dH^n = ofReal(normDet L) integral_A g(L w) dw. For A = R^n, L(A) is the range of L.
(JC) Continuity of the Jacobian (SimonGMT Chapter02.continuous_normDet, AreaApproximation.lean:28). L -> normDet L is continuous on R^n ->L[R] R^(n+l). Hence, if G is C^1, then v -> JG(v) = normDet(DG(v)) is continuous.
(Sc) Affine change of variables on R^n. For r > 0, u in R^n and Borel g : R^n -> [0, infinity], integral g(u + r w) dw = r^-n integral g(v) dv. This follows from translation invariance of L^n and L^n(rE) = r^n L^n(E) (Mathlib Measure.addHaar_smul, Measure.map_addHaar_smul).
(DCT) Dominated convergence along a countably generated filter (Mathlib MeasureTheory.tendsto_integral_filter_of_dominated_convergence). The filter of right neighbourhoods of 0 in R is countably generated.
(PC) Sibling projection_continuity (reused accepted declaration Submission.aetp_starProjection_range_continuousOn; it is a declared dependency, so its accepted candidate is present in this child's worktree). For all n, l, the map L -> (LinearMap.range L.toLinearMap).starProjection is continuous, for the operator-norm topologies, on the set {L : R^n ->L[R] R^(n+l) | L injective}.
Lean notes.
 - Some of these tools live in SimonGMT modules that the contract does not import: Chapter02.AreaCritical, Chapter02.WeightedArea, Chapter02.AreaLinearWeighted, Chapter02.AreaApproximation, Chapter02.Lipschitz, Chapter01.Lusin and Chapter02.WhitneyExtension. The Lean file proving this child adds these imports; Submission.lean imports are not byte-checked, and only the frozen definitions must stay unchanged. All of these modules except WhitneyExtension are prebuilt in the pinned package directory. WhitneyExtension (388 lines, sorry-free, axioms propext, Classical.choice and Quot.sound) has no prebuilt .olean, but its imports WhitneyJet and WhitneyPartition are prebuilt; Lake builds it on first use. If that build is unavailable in the proving or comparator environment, copy its source into Submission.lean (only exists_contDiff_one_extension_of_whitney is needed); a verbatim copy compiled in this run's decomposition audits.
 - Bochner forms that make the reduction to f >= 0 in C1(a) unnecessary are also available: SimonGMT Chapter02.integral_area_formula_of_injective_derivative (under the hypotheses of (AF)(ii), the integral over G(s) of g dH^n equals the integral over s of JG(v) g(G(v)) dH^n(v), for every g); Chapter02.measurePreserving_linearMap_normDet_smul (an injective linear L is measure preserving from ofReal(normDet L) H^n to H^n restricted to the range of L); and the exact scaling identity of (S), (H^n restricted to eta_(x,r)(E)) mapped by z -> x + r z equals ofReal(r^-1)^n (H^n restricted to E) (SimonGMT Chapter04.map_inverse_blowUp_carrier and Chapter04.hausdorff_blowUp_image; these general blow-up lemmas do not involve the excluded Chapter04.RectifiableVarifold). With these, C1(b) holds verbatim for signed f. Either route proves C1.

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

Part B. C^1 chart cover of M (Simon Ch. 3, Lemma 1.2 "only if", and Remark 1.3).
B1. By hypothesis (CountablyRectifiable n M), M is contained in M_0 union the union over j in N of F_j(R^n), with H^n(M_0) = 0 and F_j : R^n -> R^(n+l) Lipschitz. For all j in N and i >= 1, Claim A (with N = n + l and eps = 1/i) gives a C^1 map G_ij : R^n -> R^(n+l) with L^n({F_j != G_ij}) < 1/i.
 Then Z_j := the intersection over i of {F_j != G_ij} has L^n(Z_j) <= 1/i for every i, so L^n(Z_j) = 0. By (AF)(iii), H^n(F_j(Z_j)) = 0, since F_j is Lipschitz and H^n = L^n on R^n. Every v not in Z_j satisfies F_j(v) = G_ij(v) for some i, so F_j(R^n) is contained in F_j(Z_j) union the union over i of G_ij(R^n).
B2. Fix one of the C^1 maps G := G_ij and let O := {v : DG(v) is injective}.
 - O is open. Let DG(u) be injective. As n >= 1, the unit sphere of R^n is nonempty and compact, so c_u := min_(|w|=1) |DG(u)w| exists, and c_u > 0. Then |DG(u)w| >= c_u |w| for all w. Every linear map L with ||L - DG(u)|| < c_u is injective, since |Lw| >= (c_u - ||L - DG(u)||) |w|. Finally DG is continuous, as G is C^1.
 - G(R^n minus O) is H^n-null by (AF)(i), since G is differentiable everywhere and R^n minus O is its critical set {v : G is differentiable at v and DG(v) is not injective}.
 - For u in O choose sigma_u > 0 with B_(sigma_u)(u) contained in O and ||DG(v) - DG(u)|| <= c_u/2 for |v - u| <= sigma_u. Apply the mean value inequality (Mathlib Convex.norm_image_sub_le_of_norm_fderiv_le) to v -> G(v) - DG(u)v on the convex ball. Its derivative DG(v) - DG(u) has norm <= c_u/2, so |G(v) - G(v') - DG(u)(v - v')| <= (c_u/2) |v - v'|. Hence |G(v) - G(v')| >= |DG(u)(v - v')| - (c_u/2) |v - v'| >= (c_u/2) |v - v'| for v, v' in B^o_(sigma_u)(u).
 - R^n is second countable, so it has the Lindelof property (Mathlib TopologicalSpace.isOpen_iUnion_countable). Hence there is a countable set U_ij of points of O_ij := O whose balls B^o_(sigma_u)(u), u in U_ij, cover O_ij.
B3. Enumeration. The set I of triples (j, i, u) with j in N, i >= 1 and u in U_ij is countable. Hence I union {*}, where * is an extra padding symbol, is countable and nonempty, and there is a surjection k -> iota(k) from N onto it.
 - If iota(k) = (j, i, u), put G_k := G_ij, B_k := B^o_(sigma_u)(u) and c_k := c_u/2.
 - If iota(k) = *, put G_k := the zero map, B_k := B^o_0(0) = empty set and c_k := 1.
 Let N_k := G_k(B_k). By B2, for every k:
 - G_k is C^1, B_k is an open ball (possibly empty), and c_k > 0;
 - DG_k(v) is injective for v in B_k;
 - |G_k(v) - G_k(v')| >= c_k |v - v'| for v, v' in B_k.
 Let N_ex := M_0 union (the union over j of F_j(Z_j)) union (the union over (j, i) of G_ij(R^n minus O_ij)). It is a countable union of H^n-null sets (B1, B2), so H^n(N_ex) = 0.
 Every x in M lies in N_ex or in some N_k. By B1, either x is in M_0, or x = F_j(v) with v in Z_j, or x = F_j(v) = G_ij(v) for some i. In the last case, either v is not in O_ij, so x is in G_ij(R^n minus O_ij); or v is in O_ij. Then v lies in a chosen ball B^o_(sigma_u)(u) with u in U_ij, and x = G_k(v) is in N_k for any k with iota(k) = (j, i, u). Hence M minus the union over k of N_k is contained in N_ex.
B4. Consequences for each k.
 - G_k is injective on B_k, by the lower bound with c_k > 0. Let u_k : R^(n+l) -> R^n be an inverse of G_k on B_k (Mathlib Function.invFunOn G_k B_k): for x in N_k, u_k(x) is in B_k and G_k(u_k(x)) = x, and u_k(G_k(v)) = v for v in B_k. It is (1/c_k)-Lipschitz on N_k, since |u_k(x) - u_k(x')| <= c_k^-1 |G_k(u_k(x)) - G_k(u_k(x'))| = c_k^-1 |x - x'|. In particular u_k is continuous on N_k and maps N_k into B_k.
 - N_k is Borel. Write B_k = B^o_s(b). For s <= 0 it is empty. For s > 0, B_k is the union over m in N of the closed balls B_(s - 1/(m+1))(b) (empty when s - 1/(m+1) < 0). Each closed ball is compact, as R^n is proper, and G_k is continuous. So N_k is a countable union of compact, hence closed, sets.
 - H^n(N_k) < infinity. If B_k is empty, so is N_k. Otherwise the closure of B_k is compact and DG_k is continuous, so ||DG_k(v)|| <= L_k for v in B_k, for some L_k >= 0. As B_k is convex, the mean value inequality (Mathlib Convex.norm_image_sub_le_of_norm_fderiv_le) shows that G_k is L_k-Lipschitz on B_k. By (AF)(iii), H^n(N_k) <= L_k^n H^n(B_k) = L_k^n L^n(B_k) < infinity, since B_k is bounded.

Part C. The tangent field of N_k and blow-ups (the C^1 case of Simon Ch. 3, Theorem 1.6).
C0. Definition of T_k. For every x in R^(n+l) put T_k(x) := LinearMap.range (fderiv R G_k (u_k x)).toLinearMap = DG_k(u_k(x))(R^n). For x in N_k this is the plane called T_x N_k in the parent proof; the values for x not in N_k are irrelevant, since (iii) and (iv) only concern x in N_k. For x in N_k, DG_k(u_k(x)) is injective because u_k(x) is in B_k (B3), so finrank T_k(x) = finrank R^n = n (Mathlib LinearMap.finrank_range_of_inj).
C1. Claim: for every k, x in N_k and f in C_c, integral_(eta_(x,r)(N_k)) f dH^n -> integral_(T_k(x)) f dH^n as r -> 0+. Let u := u_k(x). Then u is in B_k, x = G_k(u) and T_k(x) = DG_k(u)(R^n). Put L := DG_k(u).
 (a) Reduction to f >= 0. Write f = f^+ - f^-, where f^+ := max(f, 0) and f^- := max(-f, 0) are nonnegative functions in C_c. All the integrals involved are finite.
 - H^n(eta_(x,r)(N_k)) = r^-n H^n(N_k) < infinity by (S) and B4, and f is bounded and continuous, so f is integrable on eta_(x,r)(N_k).
 - L is injective, so |Lw| >= c |w| for some c > 0 and every w. Hence L^-1(K) is bounded for every compact K. By (LinA) with g = the indicator of K, H^n(T_k(x) cap K) = ofReal(normDet L) L^n(L^-1(K)) < infinity, so f is integrable on T_k(x).
 Both sides of the claim are therefore linear in f, and it suffices to prove the claim for f >= 0. Assume this from now on.
 (b) Change of variables. Fix r > 0 and apply (S) with E = N_k (Borel by B4). Then apply (AF)(ii) to G_k on the Borel set B_k, where G_k is differentiable with injective derivative and injective. Use the continuous function h(z) := f((z - x)/r) >= 0. This gives
 integral_(eta_(x,r)(N_k)) f dH^n = r^-n integral_(N_k) f((z - x)/r) dH^n(z) = r^-n integral_(B_k) JG_k(v) f((G_k(v) - x)/r) dv.
 By (Sc) with v = u + r w, this equals integral_(R^n) phi_r(w) dw, where phi_r(w) := 1_(B_k)(u + r w) JG_k(u + r w) f((G_k(u + r w) - G_k(u))/r). All quantities are finite and nonnegative, so these lintegral identities are identities of Bochner integrals.
 (c) Domination. Let f = 0 outside B_(R_f)(0) and 0 <= f <= S_f. Suppose u + r w is in B_k and |w| > R_f/c_k. By B3, |G_k(u + r w) - G_k(u)| >= c_k r |w| > r R_f, so f((G_k(u + r w) - G_k(u))/r) = 0. Let J_k be the maximum of JG_k over the compact closure of B_k; it is finite by (JC). Hence, for all r > 0 and all w,
 0 <= phi_r(w) <= S_f J_k 1_(B_(R_f/c_k)(0))(w),
 and the right side is integrable on R^n. Each phi_r is measurable: it is the product of the indicator of the open set (B_k - u)/r and a continuous function.
 (d) Pointwise limit. Fix w. B_k is open and contains u, so u + r w is in B_k for all small r > 0. G_k is differentiable at u, so (G_k(u + r w) - G_k(u))/r -> L w as r -> 0+. Also f is continuous, and JG_k(u + r w) -> JG_k(u) by (JC). Hence phi_r(w) -> JG_k(u) f(L w).
 (e) By (DCT), integral phi_r -> integral_(R^n) JG_k(u) f(L w) dw as r -> 0+. Apply (LinA) with A = R^n and g = f. Since normDet L = JG_k(u) and L(R^n) = T_k(x), the limit equals integral_(T_k(x)) f dH^n.
 Thus C1 holds. Together with C0, this gives HasApproximateTangentSpaceAt n N_k x (T_k x) for every x in N_k.
C2. x -> p_(T_k(x)) is continuous on N_k.
 - x -> u_k(x) is continuous on N_k and maps N_k into B_k (B4).
 - u -> DG_k(u) = fderiv R G_k u is continuous on R^n, because G_k is C^1 (Mathlib ContDiff.continuous_fderiv), and DG_k(u) is injective for u in B_k (B3).
 - Hence x -> DG_k(u_k(x)) is continuous on N_k and maps N_k into the set {L : R^n ->L[R] R^(n+l) | L injective}.
 - By (PC), L -> (LinearMap.range L.toLinearMap).starProjection is continuous on that set. By composition (Mathlib ContinuousOn.comp), x -> (LinearMap.range (DG_k(u_k(x))).toLinearMap).starProjection = p_(T_k(x)) is continuous on N_k.
 (This is the parent's C2. The sibling (PC) proves its linear-algebra part: for injective L, L^T L is invertible, P_L := L (L^T L)^-1 L^T is self-adjoint and idempotent with range L(R^n), so P_L = p_(L(R^n)), and L -> P_L is continuous on injective L because the adjoint and composition are continuous and inversion is continuous at invertible operators.)

Part D. Conclusion. The sets N_k and maps T_k (k in N) satisfy:
 (i) N_k is Borel measurable (B4);
 (ii) H^n(N_k) < infinity (B4);
 (iii) x -> (T_k x).starProjection is continuous on N_k (C2);
 (iv) HasApproximateTangentSpaceAt n N_k x (T_k x) for every x in N_k (C0 and C1);
 (v) M minus the union over k of N_k is contained in N_ex (B3), so H^n(M minus the union over k of N_k) <= H^n(N_ex) = 0.
This proves the statement.

## Key steps

1. Claim A (Simon Ch. 2 Thm 1.5): Rademacher; Borel remainder suprema Rsup_k computed on a countable dense set; Egorov for Rsup_k and Lusin for the partial derivatives on the bounded shells S_m; a closed locally finite union A with L^n(R^n minus A) < eps
2. On A, Df is continuous (each K_m is a relative neighbourhood) and the Taylor remainders are uniformly small on compacts, so HasWhitneyC1Compatibility A f Df holds; Whitney gives a C^1 g = f on A; apply componentwise with tolerances summing to eps
3. Each Lipschitz piece F_j agrees with C^1 maps G_ij off the L^n-null set Z_j, and H^n(F_j(Z_j)) = 0 by the Lipschitz image bound
4. Critical images G_ij(R^n minus O_ij) are H^n-null (area formula); the mean value inequality gives bi-Lipschitz balls around points of O_ij; Lindelof and an enumeration with empty padding give charts (G_k, B_k, c_k), k in N, with M minus the union of N_k = G_k(B_k) contained in an H^n-null set
5. N_k is sigma-compact, hence Borel; it has finite H^n-measure because G_k is Lipschitz on the convex ball B_k; the inverse u_k = invFunOn G_k B_k is (1/c_k)-Lipschitz on N_k
6. T_k(x) := range DG_k(u_k x) has dimension n; blow-ups of N_k at x converge to T_k(x) by scaling, the area formula on B_k, the substitution v = u + r w, dominated convergence and the linear area formula
7. x -> p_(T_k x) is continuous on N_k: compose the continuous inverse u_k (mapping N_k into B_k), the continuous derivative DG_k (injective on B_k) and the sibling projection_continuity

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; diff GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean (IDENTICAL); cmp /tmp/tsa2-dec/GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean (identical)`
- `cat <run>/nodes/root-lipschitz-approximation-a1-tangent-structure-a1/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-v2.json,decomposition-scope-v1.json}`
- `python3 -I: dag.json node count (199), status counts, nodes with status accepted/proved/integrating and their lean_name/lean_statement; nodes whose id or lean_name match tangent|rectif|c1|chart|lusin|whitney|upper_dens|density_from|weighted`
- `grep -n max_nodes .humanize/swarm-configs/89dda8c615714b438189871eeedd71e7.json (max_nodes 200); sed -n 1760,2010p /runtime/flows/gmt-claude-a2c7949d39d0/_recursive_lean/runtime.py (_solve_children node bound and reuse mapping)`
- `sed -n 1380,1560p runtime.py (_decompose name checks before and after the audit); grep -n 'def _existing_lean_name_problem' -A 40 runtime.py; sed -n 60,260p _recursive_lean/store.py (Store.refresh, Store.update)`
- `sed -n 935,950p _recursive_lean/github_runtime.py (status accepted and candidate_commit set in one update); sed -n 997,1010p github_runtime.py and 3151,3190p runtime.py (_overlay_accepted_children); sed -n 4274,4410p runtime.py (_workspace_payload); sed -n 30,60p root_delivery.py (dependency_candidates); sed -n 2000,2060p runtime.py (_wait_for_accepted_dependencies)`
- `git log --oneline -3 cfc18a0cf91fdfb9fd76e7bf19262ed872cbe8bb 9f89be4c6f3781e8d518dff64e552c3d1263533e; git diff 03dd4115..cfc18a0c and de4bba25..9f89be4c -- GMT; git diff --stat ea56075 <dispatch> -- '*.lean' (empty)`
- `git -C .swarm-worktrees/9d018730eb17383328f7/gmt-ch05 log --oneline -8; grep -n '^theorem|^namespace|^end ' GMT/Ch05/Submission.lean (allard_graph overlay of three reused candidates)`
- `ls -la --time-style=full-iso <run>/nodes/root-density-one-regularity-a1-carrier-support-null-a1-upper-density-null-a1 <run>/nodes/root-tilt-excess-height-estimate-a1-ae-tangent-planes-a1-projection-c-ed781ad605 (accepted-candidate.json at 01:16:37Z and 01:46:53Z)`
- `python3 -I: parent-supplied-natural-proof.json proof and key_steps of both reused nodes (proof equals handoff natural_proof)`
- `grep -n '^theorem|^def' SimonGMT/Chapter03/Rectifiable.lean; sed -n 1,130p and 210,365p (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt, HasWeightedApproximateTangentSpaceAt and .unique)`
- `sed -n 1,200p GMT/Ch05/Contract.lean (RectifiableVarifold, weight, tangentProj, HasDensity, hsNormSq); sed -n 28,45p and 115,140p GMT/Ch05/README.md`
- `grep -n 'theorem exists_isClosed_continuousOn_of_measurable' -A 14 Chapter01/Lusin.lean; grep -n 'structure HasWhitneyC1Compatibility' -A 14 Chapter02/WhitneyJet.lean; grep -n 'theorem exists_contDiff_one_extension_of_whitney' -A 8 Chapter02/WhitneyExtension.lean`
- `grep -n 'theorem area_image_criticalSet_eq_zero|theorem weighted_area_formula_volume_of_injective_derivative|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|theorem weighted_linear_area_formula|theorem continuous_normDet|theorem integral_area_formula_of_injective_derivative|theorem measurePreserving_linearMap_normDet_smul|def areaJacobianAt' SimonGMT/Chapter02/*.lean`
- `grep -n '^theorem|^def' SimonGMT/Chapter04/TangentDensity.lean SimonGMT/Chapter04/WeightedBlowUp.lean; sed -n 1,130p WeightedBlowUp.lean; sed -n 25,115p TangentDensity.lean`
- `ls lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 (WhitneyExtension.olean absent; WhitneyJet, WhitneyPartition prebuilt); wc -l WhitneyExtension.lean; cat /tmp/lats-independent-audit-epgihj9r/{whitney,axioms}.log`
- `grep -rn 'theorem starProjection_norm_le|lemma Measure.integrableOn_of_bounded|theorem lintegral_ofReal_le_lintegral_enorm|theorem ofReal_le_enorm' <snapshot>/mathlib/Mathlib`
- `LEAN_PATH=$(cat /tmp/tsa2-dec/leanpath.txt) lean /tmp/tsa3-dec/check/Children.lean (three child types + usage tests)`
- `LEAN_PATH=$(cat /tmp/tsa2-dec/leanpath.txt) lean /tmp/tsa3-dec/check/Skel.lean (#print axioms GMT.Ch05.skel_parent)`
- `python3 -I /tmp/tsa3-scripts/validate.py verifier/lean_contract.py <run>/dag.json /tmp/tsa3-scripts/stmts.json`
- `grep -rl lipts_rectifiable_tangent_chart_cover <run>/{dag.json,DAG.md,dag.mmd,issue-workers.json,problem.json} GMT .lake/packages/simongmt/Poincare <run>/nodes`
- `gmt-compare.py: grep -n 'lake|build|olean' (comparator runs lake env comparator with .lake/packages symlinked to the pinned package directory)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-tangent-structure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-tangent-structure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-tangent-structure-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-tangent-structure-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-carrier-support-null-a1-upper-density-null-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-carrier-support-null-a1-upper-density-null-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-ae-tangent-planes-a1-projection-c-ed781ad605/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-ae-tangent-planes-a1-projection-c-ed781ad605/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-allard-graph-a1/speculative-prompt-v3.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/89dda8c615714b438189871eeedd71e7.json`
- `/runtime/flows/gmt-claude-a2c7949d39d0/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-a2c7949d39d0/_recursive_lean/github_runtime.py`
- `/runtime/flows/gmt-claude-a2c7949d39d0/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-a2c7949d39d0/_recursive_lean/root_delivery.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLinearWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Norm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/tsa3-dec/check/Children.lean`
- `/tmp/tsa3-dec/check/Skel.lean`
- `/tmp/tsa3-scripts/validate.py`
- `/tmp/tsa3-scripts/stmts.json`

Pinned versions. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d; the pinned SimonGMT is 2b3663083f3fe399b6296fb8eaee52169170e197. GMT/Ch05/Submission.lean is byte-identical to the snapshot copy and to Contract.lean.
Budget and reuse. The DAG holds 199 of max_nodes = 200 nodes, so at most one new child can be activated (runtime.py:1855-1866). Two accepted declarations match ingredients of the supplied proof and have byte-identical frozen types:
- upperDensity_ne_zero_outside_hausdorff_null, at root.density_one_regularity-a1.carrier_support_null-a1.upper_density_null-a1 (accepted 01:16:37Z, candidate cfc18a0c), is tool (UD);
- aetp_starProjection_range_continuousOn, at root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.projection_continuity-a1 (accepted 01:46:53Z, candidate 9f89be4c), is the linear algebra of C2.
Each candidate adds only its theorem to Submission.lean, on a dispatch base with no Lean changes. The controller refreshed its DAG at 01:47:32Z, so both are accepted checkpoints there. That removes the cause of the earlier rejection, which was a stale view taken before acceptance; _existing_lean_name_problem allows this reuse. The overlay mechanism is proven by allard_graph's three merged reused candidates.
Checked tools for the new child, all present with the stated signatures:
- in SimonGMT: Lusin (Chapter01/Lusin.lean:127); HasWhitneyC1Compatibility (WhitneyJet.lean:34) and Whitney (WhitneyExtension.lean:373, not prebuilt; its imports are prebuilt; an independent rebuild had standard axioms only); area_image_criticalSet_eq_zero (AreaCritical.lean:185); weighted_area_formula_volume_of_injective_derivative and integral_area_formula_of_injective_derivative (WeightedArea.lean:120, 151); euclideanHausdorffMeasure_image_le_of_lipschitzOn (Lipschitz.lean:216); weighted_linear_area_formula and measurePreserving_linearMap_normDet_smul (AreaLinearWeighted.lean:51, 27); continuous_normDet (AreaApproximation.lean:28); the general blow-up lemmas hausdorff_blowUp_image and map_inverse_blowUp_carrier (Chapter04; independent of the excluded Chapter04.RectifiableVarifold);
- in Mathlib: starProjection_norm_le, Measure.integrableOn_of_bounded and lintegral_ofReal_le_lintegral_enorm, used by the parent's Part H.
Not available anywhere as a theorem: the C^1 approximation theorem (Simon Ch. 2 Thm 1.5) and existence of approximate tangent planes (Ch. 3 Thm 1.6/1.9). The new child supplies Parts A-C of these from the printed proofs.
Lean results:
- check/Children.lean: all three exact child types elaborate in the replayed contract scope, with only sorry warnings, and the usage tests compile, including the new child's C2 composition with the reused lemma;
- check/Skel.lean: the parent's exact frozen conclusion follows sorry-free (axioms propext, Classical.choice, Quot.sound) from the chart-cover interface and the outputs of Parts D-E and F;
- validate_lean_statement accepts all three statements;
- the new name lipts_rectifiable_tangent_chart_cover is unreserved.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
