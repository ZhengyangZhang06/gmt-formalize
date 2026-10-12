<!-- theorem-id: gmt-ch05/root.density_one_regularity-a1.density_ge_one-a1.density_usc-a1 -->

## Theorem `Submission.exists_density_upperSemicontinuous_of_locallyLp`

Let n >= 1, U an open subset of R^(n+l), V = v(M, theta) a rectifiable n-varifold in U with weight mu, H : R^(n+l) -> R^(n+l) such that V has generalized mean curvature H in U, p > n real with H locally in L^p(mu) on U (int_K |H|^p dmu < infinity for compact K contained in U), and assume (G2) x -> P_x := tangentProj_V(x) is mu-a.e. strongly measurable and (G1) for mu-a.e. x, P_x is the orthogonal projection onto an n-dimensional subspace. Then for every xi in U there is a real d >= 0 with Theta^n(mu, xi) = d, i.e. mu(B_r(xi))/(omega_n r^n) -> d as r -> 0+ (closed balls; V.HasDensity xi d), and Theta^n(mu, .) is upper semicontinuous at xi: for every eps > 0 there is a neighbourhood N of xi such that every y in N and every real t with V.HasDensity y t satisfy t <= d + eps.

Node: `root.density_one_regularity-a1.density_ge_one-a1.density_usc-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/434

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/962

Decomposition children: None

## Lean problem

Declaration: `Submission.exists_density_upperSemicontinuous_of_locallyLp`

```lean
∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), 1 ≤ n → IsOpen U → (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ ξ ∈ U, ∃ d : ℝ, 0 ≤ d ∧ V.HasDensity ξ d ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 ξ, ∀ t : ℝ, V.HasDensity y t → t ≤ d + ε
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

- Parent DAG node: `root.density_one_regularity-a1.density_ge_one-a1`
- Child DAG node: `root.density_one_regularity-a1.density_ge_one-a1.density_usc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 4, 4.9 (density exists everywhere in U and is upper semicontinuous), with the argument of 3.11. This is steps 6 and 7 of the parent proof, written with the explicit monotone quantity of the sibling child lp_monotonicity. Notation: mu := V.weight; B_t(y) := closed ball; omega_n := unitBallVolume n = pi^(n/2)/Gamma(n/2 + 1) > 0 (Gamma > 0 on (0, infinity)); kappa := (p-n)/(4p) > 0; a := 1 - n/p in (0,1).

1. Set-up. Fix xi in U. Since U is open, choose R > 0 with B_{2R}(xi) contained in U. Every compact K contained in U has mu(K) = int over M cap K of theta dH^n < infinity (structure field integrableOn_mult). In particular mu(B_t(y)) <= mu(B_{2R}(xi)) < infinity whenever B_t(y) is contained in B_{2R}(xi). Let A* := int over B_{2R}(xi) of |H|^p dmu; it is finite by the local L^p hypothesis. Put s* := (R^(p-n) A*)^(1/p) < infinity and Lambda := s*/kappa >= 0, so kappa Lambda = s*. For y in B_R(xi), the triangle inequality gives B_R(y) contained in B_{2R}(xi), hence in U. Then
(R^(p-n) int over B_R(y) of |H|^p dmu)^(1/p) <= (R^(p-n) A*)^(1/p) = kappa Lambda,
by monotonicity of the integral in the domain and of u -> u^(1/p). So the sibling child lp_monotonicity applies at every y in B_R(xi), with radius R and this Lambda: with f(sigma) := exp((Lambda/2)(sigma/R)^a), the function G_y(sigma) := f(sigma)(sigma^(-n) mu(B_sigma(y)) + 1) is nondecreasing on (0, R]. Put m_y(sigma) := sigma^(-n) mu(B_sigma(y)) for 0 < sigma <= R, a finite nonnegative real number.

2. The factor. f is continuous on R, since a > 0 makes sigma -> (sigma/R)^a continuous. Also f(0) = exp(0) = 1, so f(sigma) -> 1 as sigma -> 0+, and f > 0.

3. Densities as real limits. Let y be in B_R(xi) and t real with V.HasDensity y t, i.e. mu(B_sigma(y))/(omega_n sigma^n) -> t^+ := max(t, 0) in [0, infinity] as sigma -> 0+. Indeed ENNReal.ofReal t = ENNReal.ofReal t^+. For 0 < sigma <= R this quotient is the finite number m_y(sigma)/omega_n, since mu(B_sigma(y)) < infinity and omega_n sigma^n > 0. Applying ENNReal.toReal, which is continuous at the finite limit ENNReal.ofReal t and maps it to t^+, gives m_y(sigma)/omega_n -> t^+, i.e. m_y(sigma) -> omega_n t^+ as sigma -> 0+.

4. Existence of the density at xi (parent step 6). G_xi is nondecreasing on (0, R] and G_xi >= 0. So the limit L := lim_{sigma -> 0+} G_xi(sigma) = inf over (0,R) of G_xi exists in R. By step 2, m_xi(sigma) = G_xi(sigma)/f(sigma) - 1 -> L - 1 =: g0, and g0 >= 0 since m_xi >= 0. Put d := g0/omega_n >= 0. For 0 < sigma <= R the density quotient of V at xi equals ENNReal.ofReal(m_xi(sigma)/omega_n), and m_xi(sigma)/omega_n -> d. Since ENNReal.ofReal is continuous, V.HasDensity xi d.

5. A lower bound at nearby points. Let y be in B_R(xi), t real with V.HasDensity y t, and tau in (0, R]. For 0 < sigma <= tau, monotonicity gives G_y(sigma) <= G_y(tau). As sigma -> 0+, G_y(sigma) = f(sigma)(m_y(sigma) + 1) -> 1 * (omega_n t^+ + 1) by steps 2 and 3. Hence omega_n t^+ + 1 <= G_y(tau).

6. Choice of scales (parent step 7). Fix eps > 0 and put T := omega_n (d + eps) + 1. As tau -> 0+, f(tau)(m_xi(tau) + 1) -> 1 * (g0 + 1) = omega_n d + 1 < T. So there is tau in (0, R/2) with f(tau)(m_xi(tau) + 1) < T. Next, the closed balls B_{tau+delta}(xi), delta > 0, decrease to their intersection B_tau(xi), and mu(B_{tau + R/2}(xi)) <= mu(B_{2R}(xi)) < infinity. By continuity of measure from above, mu(B_{tau+delta}(xi)) -> mu(B_tau(xi)) as delta -> 0+, hence f(tau)(tau^(-n) mu(B_{tau+delta}(xi)) + 1) -> f(tau)(m_xi(tau) + 1) < T. So there is delta in (0, R/2) with f(tau)(tau^(-n) mu(B_{tau+delta}(xi)) + 1) < T.

7. Conclusion. Let N be the open ball of radius delta about xi; it is a neighbourhood of xi. Let y be in N and t real with V.HasDensity y t. Then y is in B_R(xi) because delta < R. Also B_tau(y) is contained in B_{tau+delta}(xi) by the triangle inequality, and tau <= R. By step 5, monotonicity of mu and f(tau) > 0:
omega_n t^+ + 1 <= G_y(tau) = f(tau)(tau^(-n) mu(B_tau(y)) + 1) <= f(tau)(tau^(-n) mu(B_{tau+delta}(xi)) + 1) < T = omega_n (d + eps) + 1.
Since omega_n > 0, t <= t^+ < d + eps. This holds for every y in N and every such t, which is the asserted upper semicontinuity. Together with step 4 this proves the claim. QED.

Formalization notes (not part of the argument): the appendix below gives a complete Lean proof of this child from the frozen type of lp_monotonicity, compiled during the decomposition. Ingredients:
- MonotoneOn.tendsto_nhdsWithin_Ioo_right (the limit in step 4).
- ENNReal.tendsto_toReal and ENNReal.toReal_ofReal' (step 3).
- ENNReal.ofReal_div_of_pos and ENNReal.ofReal_toReal (step 4).
- tendsto_measure_cthickening_of_isClosed with cthickening_closedBall (step 6).
- Real.Gamma_pos_of_pos (omega_n > 0).
- Ioc_mem_nhdsGT and Ioo_mem_nhdsGT.

APPENDIX (formal reference, not part of the mathematical proof). Complete Lean proof of this exact frozen statement from the frozen type of the sibling `lp_corrected_mass_ratio_monotoneOn` (child lp_monotonicity). It was compiled during the decomposition review (Lean v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d, simongmt 2b3663083f3fe399b6296fb8eaee52169170e197) after lines 1-460 of GMT/Ch05/Contract.lean, inside `namespace Submission`. No extra imports are needed. Together with the appendices of the two siblings, `#print axioms Submission.exists_density_upperSemicontinuous_of_locallyLp` reports [propext, Classical.choice, Quot.sound].
```lean
theorem exists_density_upperSemicontinuous_of_locallyLp : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), 1 ≤ n → IsOpen U → (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ ξ ∈ U, ∃ d : ℝ, 0 ≤ d ∧ V.HasDensity ξ d ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 ξ, ∀ t : ℝ, V.HasDensity y t → t ≤ d + ε := by
  intro n ℓ U V H p hn hU hp hH hLp hG2 hG1 ξ hξ
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    apply div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    apply Real.Gamma_pos_of_pos
    positivity
  set ω := unitBallVolume n with hω_def
  -- local finiteness of the weight on compact subsets of `U`
  have hfin : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U → V.weight K < ∞ := by
    intro K hK hKU
    have hint := V.integrableOn_mult K hK hKU
    rw [RectifiableVarifold.weight, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, Set.inter_comm]
    exact hint.lintegral_lt_top
  obtain ⟨R, hR, hball⟩ : ∃ R > 0, closedBall ξ (2 * R) ⊆ U := by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU ξ hξ
    refine ⟨r / 4, by positivity, ?_⟩
    exact (closedBall_subset_ball (by linarith)).trans hsub
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  set κ : ℝ := (p - n) / (4 * p) with hκ_def
  have hκ : 0 < κ := div_pos (sub_pos.mpr hp) (by positivity)
  set A := ∫⁻ x in closedBall ξ (2 * R), ‖H x‖ₑ ^ p ∂V.weight with hA_def
  have hA : A < ∞ := hLp _ (isCompact_closedBall _ _) hball
  set s : ℝ≥0∞ := (ENNReal.ofReal (R ^ (p - n)) * A) ^ (1 / p) with hs_def
  have hs : s ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA.ne
  set Λ : ℝ := s.toReal / κ with hΛ_def
  have hΛ : 0 ≤ Λ := div_nonneg ENNReal.toReal_nonneg hκ.le
  have hκΛ : ENNReal.ofReal (κ * Λ) = s := by
    rw [hΛ_def, mul_div_cancel₀ _ hκ.ne', ENNReal.ofReal_toReal hs]
  have hsub2 : ∀ y ∈ closedBall ξ R, closedBall y R ⊆ closedBall ξ (2 * R) := by
    intro y hy
    apply closedBall_subset_closedBall'
    have : dist y ξ ≤ R := hy
    linarith
  have hscale : ∀ y ∈ closedBall ξ R, V.scaledLpNorm H p y R ≤ ENNReal.ofReal (κ * Λ) := by
    intro y hy
    rw [hκΛ, RectifiableVarifold.scaledLpNorm]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    exact mul_le_mul_right (lintegral_mono_set (hsub2 y hy)) _
  set f : ℝ → ℝ := fun σ => Real.exp (Λ / 2 * (σ / R) ^ (1 - (n : ℝ) / p)) with hf_def
  set G : Amb n ℓ → ℝ → ℝ := fun y σ =>
    f σ * ((V.weight (closedBall y σ)).toReal / σ ^ n + 1) with hG_def
  have hmono : ∀ y ∈ closedBall ξ R, MonotoneOn (G y) (Ioc 0 R) := by
    intro y hy
    exact lp_corrected_mass_ratio_monotoneOn V H p hn hp hH hG2 hG1 y R Λ hR hΛ
      ((hsub2 y hy).trans hball) (hscale y hy)
  have he : 0 < 1 - (n : ℝ) / p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hf1 : Tendsto f (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous f := by
      apply Real.continuous_exp.comp
      exact continuous_const.mul
        ((continuous_id.div_const R).rpow_const (fun _ => Or.inr he.le))
    have ht := (hc.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa [hf_def, zero_div, Real.zero_rpow he.ne'] using ht
  have hfpos : ∀ σ, 0 < f σ := fun σ => Real.exp_pos _
  have hfinball : ∀ y ∈ closedBall ξ R, ∀ σ, σ ≤ R → V.weight (closedBall y σ) ≠ ∞ := by
    intro y hy σ hσ
    exact ((measure_mono (closedBall_subset_closedBall hσ)).trans_lt
      (hfin _ (isCompact_closedBall _ _) ((hsub2 y hy).trans hball))).ne
  set m : Amb n ℓ → ℝ → ℝ := fun y σ => (V.weight (closedBall y σ)).toReal / σ ^ n with hm_def
  -- conversion of `HasDensity` into a limit of real mass ratios
  have hconv : ∀ y ∈ closedBall ξ R, ∀ t : ℝ, V.HasDensity y t →
      Tendsto (m y) (𝓝[>] 0) (𝓝 (ω * max t 0)) := by
    intro y hy t ht
    have h1 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp ht
    rw [ENNReal.toReal_ofReal'] at h1
    have h2 := h1.const_mul ω
    apply h2.congr'
    filter_upwards [Ioc_mem_nhdsGT hR] with σ hσ
    have hσn : 0 < σ ^ n := pow_pos hσ.1 n
    simp only [Function.comp_apply, hm_def]
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity), ← hω_def]
    field_simp
  have hξR : ξ ∈ closedBall ξ R := mem_closedBall_self hR.le
  -- existence of the density at `ξ`
  have hne : (Ioo (0 : ℝ) R).Nonempty := ⟨R / 2, by positivity, by linarith⟩
  have hGnonneg : ∀ σ ∈ Ioo 0 R, 0 ≤ G ξ σ := fun σ hσ =>
    mul_nonneg (hfpos σ).le (add_nonneg (div_nonneg ENNReal.toReal_nonneg
      (pow_pos hσ.1 n).le) zero_le_one)
  have hGlim := MonotoneOn.tendsto_nhdsWithin_Ioo_right hne
    ((hmono ξ hξR).mono Ioo_subset_Ioc_self)
    ⟨0, by rintro _ ⟨σ, hσ, rfl⟩; exact hGnonneg σ hσ⟩
  set L := sInf (G ξ '' Ioo 0 R) with hL_def
  have hm_lim : Tendsto (m ξ) (𝓝[>] 0) (𝓝 (L - 1)) := by
    have h := (hGlim.div hf1 one_ne_zero).sub_const 1
    rw [div_one] at h
    apply h.congr'
    filter_upwards with σ
    simp only [Pi.div_apply, hG_def, hm_def]
    rw [mul_div_cancel_left₀ _ (hfpos σ).ne']
    ring
  have hL1 : 0 ≤ L - 1 := by
    apply ge_of_tendsto hm_lim
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact div_nonneg ENNReal.toReal_nonneg (pow_pos hσ n).le
  set d := (L - 1) / ω with hd_def
  have hωd : ω * d = L - 1 := by rw [hd_def]; field_simp
  refine ⟨d, div_nonneg hL1 hω.le, ?_, ?_⟩
  · -- `HasDensity ξ d`
    unfold RectifiableVarifold.HasDensity
    have h := (ENNReal.continuous_ofReal.tendsto _).comp (hm_lim.div_const ω)
    apply h.congr'
    filter_upwards [Ioc_mem_nhdsGT hR] with σ hσ
    have hσn : 0 < σ ^ n := pow_pos hσ.1 n
    simp only [Function.comp_apply, hm_def]
    rw [div_div, mul_comm (σ ^ n) ω, ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_toReal (hfinball ξ hξR σ hσ.2)]
  · intro ε hε
    set T := ω * (d + ε) + 1 with hT_def
    have hlim0 : Tendsto (fun τ => f τ * (m ξ τ + 1)) (𝓝[>] 0) (𝓝 (1 * (L - 1 + 1))) :=
      hf1.mul (hm_lim.add_const 1)
    have hlt0 : 1 * (L - 1 + 1) < T := by
      rw [← hωd, hT_def]
      nlinarith [mul_pos hω hε]
    obtain ⟨τ, hτlt, hτ⟩ :=
      ((hlim0.eventually (gt_mem_nhds hlt0)).and (Ioo_mem_nhdsGT (half_pos hR))).exists
    -- continuity from above of `δ ↦ μ(B_{τ+δ}(ξ))`
    have hcont : Tendsto (fun δ => V.weight (closedBall ξ (τ + δ))) (𝓝[>] 0)
        (𝓝 (V.weight (closedBall ξ τ))) := by
      have h := tendsto_measure_cthickening_of_isClosed (μ := V.weight)
        (s := closedBall ξ τ) ⟨R / 2, half_pos hR, by
          rw [cthickening_closedBall (half_pos hR).le hτ.1.le]
          exact hfinball ξ hξR _ (by linarith [hτ.2])⟩ isClosed_closedBall
      apply (h.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).congr'
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      rw [cthickening_closedBall (le_of_lt hδ) hτ.1.le, add_comm δ τ]
    have hcontR : Tendsto (fun δ => f τ * ((V.weight (closedBall ξ (τ + δ))).toReal / τ ^ n + 1))
        (𝓝[>] 0) (𝓝 (f τ * (m ξ τ + 1))) := by
      have h := (ENNReal.tendsto_toReal (hfinball ξ hξR τ (by linarith [hτ.2]))).comp hcont
      exact ((h.div_const (τ ^ n)).add_const 1).const_mul (f τ)
    obtain ⟨δ, hδlt, hδ⟩ :=
      ((hcontR.eventually (gt_mem_nhds hτlt)).and (Ioo_mem_nhdsGT (half_pos hR))).exists
    filter_upwards [ball_mem_nhds ξ hδ.1] with y hy t ht
    have hyξ : dist y ξ < δ := hy
    have hyR : y ∈ closedBall ξ R := by
      show dist y ξ ≤ R
      linarith [hδ.2]
    have hlimy := hconv y hyR t ht
    have hGy : Tendsto (G y) (𝓝[>] 0) (𝓝 (1 * (ω * max t 0 + 1))) :=
      hf1.mul (hlimy.add_const 1)
    have hle : 1 * (ω * max t 0 + 1) ≤ G y τ := by
      apply le_of_tendsto hGy
      filter_upwards [Ioc_mem_nhdsGT hτ.1] with σ hσ
      exact hmono y hyR ⟨hσ.1, hσ.2.trans (by linarith [hτ.2])⟩
        ⟨hτ.1, by linarith [hτ.2]⟩ hσ.2
    have hball_sub : closedBall y τ ⊆ closedBall ξ (τ + δ) := by
      apply closedBall_subset_closedBall'
      linarith
    have hGyτ : G y τ ≤ f τ * ((V.weight (closedBall ξ (τ + δ))).toReal / τ ^ n + 1) := by
      apply mul_le_mul_of_nonneg_left _ (hfpos τ).le
      have hτn : 0 < τ ^ n := pow_pos hτ.1 n
      have := ENNReal.toReal_mono (hfinball ξ hξR (τ + δ) (by linarith [hτ.2, hδ.2]))
        (measure_mono hball_sub)
      gcongr
    have h3 : ω * max t 0 < ω * (d + ε) := by linarith
    have h4 := lt_of_mul_lt_mul_left h3 hω.le
    linarith [le_max_left t 0]
```

## Key steps

1. Choose R with B_{2R}(xi) in U and Lambda = kappa^-1 (R^(p-n) int_{B_2R(xi)}|H|^p)^(1/p); lp_monotonicity applies at every y in B_R(xi) with radius R
2. HasDensity y t gives sigma^-n mu(B_sigma(y)) -> omega_n max(t,0)
3. At xi the monotone G_xi has a limit as sigma -> 0+, and the factor tends to 1, so sigma^-n mu(B_sigma(xi)) converges; this gives HasDensity xi d with d >= 0
4. Monotonicity at nearby y gives omega_n max(t,0) + 1 <= G_y(tau) <= f(tau)(tau^-n mu(B_{tau+delta}(xi)) + 1)
5. Choose tau small, then delta small by continuity from above of closed-ball measures; then t <= d + eps on the delta-ball about xi

## Reference use

### local-project

Queries:
- `python3 json.load(nodes/root-density-one-regularity-a1-density-ge-one-a1/parent-child-handoff.json): subproblem, audit, resolved_dependencies`
- `python3 scan of dag.json: lean_name / lean_statement / status of every node (reserved names; tangent_ae, aal_lp_monotonicity, aal_tangent_structure, dohr_local_monotonicity)`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `rg -n 'def HasDensity|def LocallyLp|def scaledLpNorm|def HasGeneralizedMeanCurvature|def divM|def tangentProj|def support|def weight|integrableOn_mult' <snapshot>/project/GMT/Ch05/Contract.lean`
- `rg -n 'theorem |lemma ' <snapshot>/project/GMT/Ch05/`
- `rg -n '^theorem (hasDerivAt_integral_of_dominated_loc_of_deriv_le|integral_mul_le_Lp_mul_Lq_of_nonneg|monotoneOn_of_deriv_nonneg|tendsto_integral_filter_of_dominated_convergence|tendsto_measure_cthickening_of_isClosed|cthickening_closedBall|measure_eq_zero_iff_ae_notMem|withDensity_absolutelyContinuous|Integrable.lintegral_lt_top|Gamma_pos_of_pos|contDiffAt_norm)\b' <snapshot>/mathlib/Mathlib`
- `rg -n '^(theorem|lemma) (MonotoneOn.tendsto_nhdsWithin_Ioo_right|mem_support_iff_forall|LocallyIntegrableOn.integrableOn_compact_subset)\b' <snapshot>/mathlib/Mathlib`
- `rg -n smoothTransition <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `grep -rn 'HasFDerivAt.norm|hasFDerivAt_norm|fderiv_norm|hasStrictFDerivAt_norm' Mathlib --include=*.lean`
- `grep -n '^theorem|^def' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{LpDensity,LpMeanCurvature,FirstVariation,MeanCurvature,Density,LowerDensityTangents,TangentDensity}.lean`
- `cat Chapter04/{LpLowerDensity,MultiplicityBridge,LpDensity}.lean; sed -n 1,260p Chapter04/Basic.lean; sed -n 1,563p Chapter04/LpMeanCurvature.lean; sed -n 1,320p, 390,430p, 600,960p Chapter04/FirstVariation.lean`
- `sed -n 25,130p and 225,365p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 215,575p book/chapter-04.txt`
- `grep -rl 'radial_cutoff_first_variation_eq|lp_corrected_mass_ratio_monotoneOn|exists_density_upperSemicontinuous_of_locallyLp' .humanize GMT .lake/packages/simongmt/Poincare .lake/packages/mathlib/Mathlib`
- `sed -n 1,120p, 330,384p, 500,580p verifier/gmt-compare.py (child_modules / contract_scope)`
- `lake env lean /tmp/dge1-check/Check5.lean, Check3.lean, Check4.lean, verify/A1.lean, verify/M.lean, verify/FullChain.lean, verify/FromJSON.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/MultiplicityBridge.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Density.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-density-ge-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dge1-check/Check5.lean`
- `/tmp/dge1-check/Check3.lean`
- `/tmp/dge1-check/Check4.lean`
- `/tmp/dge1-check/verify/A1.lean`
- `/tmp/dge1-check/verify/M.lean`
- `/tmp/dge1-check/verify/FromJSON.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d; its GMT/Ch05/Contract.lean is byte-identical to the workspace copy (cmp). The project contains no density or monotonicity theorem for the contract RectifiableVarifold (rg finds only definitions and the sorry'd main_theorem), so all three children are new obligations.

SimonGMT Chapter04 proves the full L^p theory: LpMeanCurvature.lean lp_normalizedBallMass_monotoneOn_Ioc with lpMonotonicityFactor = exp((Lambda/2)(rho/R)^(1-n/p)); LpDensity.lean; LpLowerDensity.lean one_le_stationaryDensityReal_of_mem_support_lp. It does so only for Chapter04.RectifiableVarifold (Basic.lean), which needs a MeasurableSet carrier, an unweighted approximate-tangent field (Chapter03 HasApproximateTangentSpaceAt) and a globally locally finite weight. The contract varifold and the sibling tangent_ae give only weighted tangents (HasWeightedApproximateTangentSpaceAt, Chapter03/Rectifiable.lean:330), so these theorems do not transfer. The generic SimonGMT lemmas do apply and are used: monotonicityCutoff (FirstVariation.lean:825ff), deriv_eq_zero_of_cutoff, hasDerivAt_lpMonotonicityFactor, and trace_radialEndomorphism as a template.

All Mathlib lemmas used are present in the snapshot:
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286)
- integral_mul_le_Lp_mul_Lq_of_nonneg (Bochner/Basic.lean:1230)
- monotoneOn_of_deriv_nonneg (Deriv/MeanValue.lean:411)
- tendsto_integral_filter_of_dominated_convergence (DominatedConvergence.lean:67)
- tendsto_measure_cthickening_of_isClosed (BorelSpace/Metric.lean:143)
- cthickening_closedBall (Ball/Pointwise.lean:318)
- measure_eq_zero_iff_ae_notMem (OuterMeasure/AE.lean:145)
- withDensity_absolutelyContinuous (WithDensity.lean:146)
- Integrable.lintegral_lt_top (IntegrableOn.lean:479)
- Real.Gamma_pos_of_pos (Gamma/Basic.lean:443)
- contDiffAt_norm (InnerProductSpace/Calculus.lean:154)
- MonotoneOn.tendsto_nhdsWithin_Ioo_right (Topology/Order/Monotone.lean:457)
- Measure.mem_support_iff_forall (Measure/Support.lean:75)
- LocallyIntegrableOn.integrableOn_compact_subset (LocallyIntegrable.lean:122)
- the Real.smoothTransition API
There is no derivative-of-norm lemma (no match for HasFDerivAt.norm or hasFDerivAt_norm), so the Lean proof of child 1 uses the squared-radius reparametrization.

The three proposed lean_names occur nowhere in .humanize, GMT, SimonGMT or Mathlib and are not among the DAG's reserved lean_names.

Lean checks:
- All three types elaborate verbatim in the child-comparator scope.
- Complete sorry-free proofs of all three children compile with axioms propext, Classical.choice, Quot.sound.
- The selected theorem compiles from the children and the sibling tangent_ae, with sorryAx only from that sibling placeholder.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
