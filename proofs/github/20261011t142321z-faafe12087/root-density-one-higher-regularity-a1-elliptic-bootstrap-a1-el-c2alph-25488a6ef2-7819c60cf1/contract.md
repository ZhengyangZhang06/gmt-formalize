<!-- theorem-id: gmt-ch05/root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.dq_weak_equation-a1 -->

## Theorem `Submission.dohr_eb_elc2_dq_weak_equation`

Let n, l be natural numbers, L := L(R^n, R^l), Psi : L -> R of class C^2 with A := D Psi and B := D^2 Psi, U and V open subsets of R^n, u, g : R^n -> R^l with u of class C^1 on U and g continuous on U, e in R^n and d a nonzero real number, such that x + (td)e lies in U for all x in V and t in [0,1]. Assume that the integral over U of A(Du(x))[Dphi(x)] dx equals minus the integral over U of <phi(x), g(x)> dx for every C^1 compactly supported phi : R^n -> R^l with tsupport phi contained in U. Then for every C^1 compactly supported zeta : R^n -> R^l with tsupport zeta contained in V: the integral over V of ( integral_0^1 B(Du(x) + t(Du(x + de) - Du(x)))[d^{-1}(Du(x + de) - Du(x))][Dzeta(x)] dt ) dx equals the integral over V of < integral_0^1 g(x + (td)e) dt , Dzeta(x)e > dx.

Node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.dq_weak_equation-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2277

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4031

Decomposition children: None

## Lean problem

Declaration: `Submission.dohr_eb_elc2_dq_weak_equation`

```lean
∀ (n ℓ : ℕ) (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (U V : Set (Rn n)) (u g : Rn n → Rn ℓ) (e : Rn n) (d : ℝ), ContDiff ℝ 2 Ψ → IsOpen U → IsOpen V → ContDiffOn ℝ 1 u U → ContinuousOn g U → d ≠ 0 → (∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ U) → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in U, inner ℝ (φ x) (g x)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ V → ∫ x in V, (∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u x + t • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (fderiv ℝ ζ x)) = ∫ x in V, inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (fderiv ℝ ζ x e)
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

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.dq_weak_equation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 4(a), (b) and (d) of the parent proof; the right-hand side computation 4(c) is the sibling dohr_eb_elc2_shift_ibp.
Notation. Delta(y) := Du(y + de) - Du(y), P_t(y) := Du(y) + t Delta(y), I(y) := integral_0^1 B(P_t(y))[d^{-1}Delta(y)][Dzeta(y)] dt, G(y) := integral_0^1 g(y + (td)e) dt and J(y) := <G(y), Dzeta(y)e>. The claim is integral_V I = integral_V J. Fix zeta as in the statement; K := tsupport zeta is compact, closed and contained in V. Lebesgue measure is translation invariant (integral_add_right_eq_self).
1. Vanishing. zeta(y) = 0 and Dzeta(y) = 0 for y not in K (fderiv_of_notMem_tsupport), so I(y) = 0 and J(y) = 0 for y not in K (both are linear in Dzeta(y)). As K is contained in V, integral_V I = integral I and integral_V J = integral J over R^n (setIntegral_eq_integral_of_forall_compl_eq_zero); it suffices to prove integral I = integral J.
2. Points of U. For y in K and t in [0,1], y + (td)e lies in U; in particular y and y + de lie in U. As U is open and u is C^1 on U, Du is continuous at every point of U (ContDiffOn.continuousOn_fderiv_of_isOpen); g is continuous at every point of U. Psi is C^2, so A is C^1 with derivative B, and A, B are continuous.
3. Continuity principle. If C is a compact subset of R^n and F : R^n -> R vanishes outside C and is continuous at every point of C, then F is continuous (a point outside the closed set C has a neighbourhood on which F = 0) and has compact support (HasCompactSupport.intro), hence is integrable (Continuous.integrable_of_hasCompactSupport).
4. Integrands. F1(y) := A(Du(y + de))[Dzeta(y)], F2(y) := A(Du(y))[Dzeta(y)] and R2(y) := <zeta(y), g(y)> vanish outside K and are continuous at every point of K (step 2). R3(x) := <zeta(x - de), g(x)> vanishes outside K + de (compact, contained in U by step 2) and is continuous at every point of K + de. By step 3 all four are integrable.
5. Test function zeta. zeta is C^1 with compact support and tsupport zeta = K is contained in U. The hypothesis gives integral_U A(Du(x))[Dzeta(x)] dx = - integral_U <zeta(x), g(x)> dx. Both integrands vanish outside K, a subset of U, so the integrals over U are integrals over R^n: (E2) integral F2 = - integral R2.
6. Translated test function. phi1(x) := zeta(x - de) is C^1 with Dphi1(x) = Dzeta(x - de) (fderiv_comp_sub); it has compact support (composition with the homeomorphism x -> x - de; HasCompactSupport.comp_isClosedEmbedding), and tsupport phi1 = K + de (tsupport_comp_eq_preimage) is contained in U. The hypothesis gives integral_U A(Du(x))[Dzeta(x - de)] dx = - integral_U <zeta(x - de), g(x)> dx. The integrands vanish outside K + de, so these are integrals over R^n; the right one is - integral R3, and translating x = y + de in the left one gives (E1) integral F1 = - integral R3. (Equivalently integral F1 = - integral <zeta(y), g(y + de)> dy, and integral <zeta(y), g(y + de)> dy = integral R3 by translation.)
7. Subtracting (E2) from (E1) and using step 4 (integral_sub): integral (F1 - F2) = integral R2 - integral R3 = integral (R2 - R3) = integral <zeta(x) - zeta(x - de), g(x)> dx (inner_sub_left).
8. Pointwise FTC. Fix y in K. h(t) := A(P_t(y)) in L* has derivative h'(t) = B(P_t(y))[Delta(y)] (chain rule: t -> P_t(y) is affine with derivative Delta(y)), continuous in t. By the fundamental theorem of calculus (intervalIntegral.integral_eq_sub_of_hasDerivAt), A(Du(y + de)) - A(Du(y)) = h(1) - h(0) = integral_0^1 B(P_t(y))[Delta(y)] dt, since P_1(y) = Du(y + de) and P_0(y) = Du(y). Evaluating at Dzeta(y) (ContinuousLinearMap.intervalIntegral_apply): F1(y) - F2(y) = integral_0^1 B(P_t(y))[Delta(y)][Dzeta(y)] dt. As Delta(y) = d (d^{-1}Delta(y)) and B(P_t(y)) is linear in its first argument, the integrand equals d B(P_t(y))[d^{-1}Delta(y)][Dzeta(y)], so F1(y) - F2(y) = d I(y). For y not in K both sides vanish (Dzeta(y) = 0). Hence integral (F1 - F2) = d integral I (integral_const_mul).
9. The sibling dohr_eb_elc2_shift_ibp, applied to (U, g, zeta, e, d) (its hypothesis is step 2: x + (td)e in U for x in tsupport zeta and t in [0,1]), gives integral <zeta(x) - zeta(x - de), g(x)> dx = d integral J.
10. Steps 7, 8 and 9 give d integral I = d integral J. Since d is nonzero, integral I = integral J, and step 1 gives integral_V I = integral_V J. QED
Instance note: the FTC in L* and the evaluation of B need set_option maxSynthPendingDepth 5 (checked; the realization below uses it).
Lean realization, checked at the pin (Lean 4.35.0-rc3, Mathlib 25730c7c): compiled inside namespace GMT.Ch05 of a scratch copy of GMT/Ch05/Submission.lean (contract opens in effect); #print axioms gives only propext, Classical.choice, Quot.sound; the NodeSolution file generated by verifier/gmt-compare.py (exact Submission.dohr_eb_elc2_dq_weak_equation) closes against it.
```lean
set_option maxSynthPendingDepth 5 in
theorem Submission.dohr_eb_elc2_dq_weak_equation : ∀ (n ℓ : ℕ) (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (U V : Set (Rn n)) (u g : Rn n → Rn ℓ) (e : Rn n) (d : ℝ), ContDiff ℝ 2 Ψ → IsOpen U → IsOpen V → ContDiffOn ℝ 1 u U → ContinuousOn g U → d ≠ 0 → (∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ U) → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in U, inner ℝ (φ x) (g x)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ V → ∫ x in V, (∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u x + t • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (fderiv ℝ ζ x)) = ∫ x in V, inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (fderiv ℝ ζ x e) := by
  intro n ℓ Ψ U V u g e d hΨ hU hV hu hg hd hseg hweak ζ hζ hζc hζV
  set K := tsupport ζ with hK_def
  have hKc : IsCompact K := hζc
  have hKcl : IsClosed K := isClosed_tsupport ζ
  have hKV : K ⊆ V := hζV
  have hsegK : ∀ y ∈ K, ∀ t ∈ Icc (0:ℝ) 1, y + (t * d) • e ∈ U := fun y hy => hseg y (hKV hy)
  have hKU : K ⊆ U := fun y hy => by simpa using hsegK y hy 0 (by simp)
  have hKdU : ∀ y ∈ K, y + d • e ∈ U := fun y hy => by simpa using hsegK y hy 1 (by simp)
  have hDuAt : ∀ y ∈ U, ContinuousAt (fderiv ℝ u) y := fun y hy =>
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hy)
  have hgAt : ∀ y ∈ U, ContinuousAt g y := fun y hy => hg.continuousAt (hU.mem_nhds hy)
  have hDζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hζcont : Continuous ζ := hζ.continuous
  have hDζ0 : ∀ y ∉ K, fderiv ℝ ζ y = 0 := fun y hy => fderiv_of_notMem_tsupport ℝ hy
  have hζ0 : ∀ y ∉ K, ζ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hA1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (by norm_num)
  have hAc : Continuous (fderiv ℝ Ψ) := hA1.continuous
  have hBc : Continuous (fderiv ℝ (fderiv ℝ Ψ)) := hA1.continuous_fderiv one_ne_zero
  have hAd : Differentiable ℝ (fderiv ℝ Ψ) := hA1.differentiable one_ne_zero
  have cont_of : ∀ (F : Rn n → ℝ) (C : Set (Rn n)), IsClosed C → (∀ y ∉ C, F y = 0) →
      (∀ y ∈ C, ContinuousAt F y) → Continuous F := by
    intro F C hC h0 hcont
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ C
    · exact hcont y hy
    · have hev : F =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
        filter_upwards [hC.isOpen_compl.mem_nhds hy] with z hz using h0 z hz
      exact continuousAt_const.congr hev.symm
  have integ_of : ∀ (F : Rn n → ℝ) (C : Set (Rn n)), IsCompact C → (∀ y ∉ C, F y = 0) →
      (∀ y ∈ C, ContinuousAt F y) → Integrable F := by
    intro F C hC h0 hcont
    exact (cont_of F C hC.isClosed h0 hcont).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hC h0)
  -- the four (five) integrands
  set F1 : Rn n → ℝ := fun y => fderiv ℝ Ψ (fderiv ℝ u (y + d • e)) (fderiv ℝ ζ y) with hF1
  set F2 : Rn n → ℝ := fun y => fderiv ℝ Ψ (fderiv ℝ u y) (fderiv ℝ ζ y) with hF2
  set R2 : Rn n → ℝ := fun y => inner ℝ (ζ y) (g y) with hR2
  set R3 : Rn n → ℝ := fun x => inner ℝ (ζ (x - d • e)) (g x) with hR3
  set Kd : Set (Rn n) := (fun y => y + d • e) '' K with hKd
  have hKdc : IsCompact Kd := hKc.image (continuous_id.add continuous_const)
  have hmemKd : ∀ x, x - d • e ∈ K → x ∈ Kd := fun x hx => ⟨x - d • e, hx, by simp⟩
  have hKdU' : Kd ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hKdU y hy
  have hF1i : Integrable F1 := by
    refine integ_of F1 K hKc (fun y hy => by simp [hF1, hDζ0 y hy]) (fun y hy => ?_)
    have h1 : ContinuousAt (fun y => fderiv ℝ u (y + d • e)) y :=
      (hDuAt _ (hKdU y hy)).comp_of_eq (continuous_id.add continuous_const).continuousAt rfl
    exact (hAc.continuousAt.comp h1).clm_apply hDζ.continuousAt
  have hF2i : Integrable F2 := by
    refine integ_of F2 K hKc (fun y hy => by simp [hF2, hDζ0 y hy]) (fun y hy => ?_)
    exact (hAc.continuousAt.comp (hDuAt y (hKU hy))).clm_apply hDζ.continuousAt
  have hR2i : Integrable R2 := by
    refine integ_of R2 K hKc (fun y hy => by simp [hR2, hζ0 y hy]) (fun y hy => ?_)
    exact hζcont.continuousAt.inner (hgAt y (hKU hy))
  have hR3i : Integrable R3 := by
    refine integ_of R3 Kd hKdc (fun x hx => ?_) (fun x hx => ?_)
    · have : x - d • e ∉ K := fun h => hx (hmemKd x h)
      simp [hR3, hζ0 _ this]
    · have h1 : ContinuousAt (fun x => ζ (x - d • e)) x :=
        (hζcont.comp (continuous_sub_right _)).continuousAt
      exact h1.inner (hgAt x (hKdU' hx))
  -- weak equation with ζ
  have hE2 : ∫ y, F2 y = -∫ y, R2 y := by
    have h := hweak ζ hζ hζc hKU
    have hl : ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ ζ x) = ∫ y, F2 y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have : x ∉ K := fun h' => hx (hKU h')
      simp [hDζ0 x this]
    have hr : ∫ x in U, inner ℝ (ζ x) (g x) = ∫ y, R2 y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have : x ∉ K := fun h' => hx (hKU h')
      simp [hζ0 x this]
    rw [hl, hr] at h
    exact h
  -- weak equation with the translate
  set φ1 : Rn n → Rn ℓ := fun x => ζ (x - d • e) with hφ1
  have hφ1C : ContDiff ℝ 1 φ1 := hζ.comp (contDiff_id.sub contDiff_const)
  have hφ1c : HasCompactSupport φ1 :=
    hζc.comp_isClosedEmbedding (Homeomorph.subRight (d • e)).isClosedEmbedding
  have hφ1ts : tsupport φ1 ⊆ U := by
    intro x hx
    have h := (tsupport_comp_eq_preimage ζ (Homeomorph.subRight (d • e))).subset hx
    have hxK : x - d • e ∈ K := h
    simpa using hKdU _ hxK
  have hφ1D : ∀ x, fderiv ℝ φ1 x = fderiv ℝ ζ (x - d • e) := fun x => fderiv_comp_sub (d • e)
  have hE1 : ∫ y, F1 y = -∫ y, inner ℝ (ζ y) (g (y + d • e)) := by
    have h := hweak φ1 hφ1C hφ1c hφ1ts
    have hl : ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ1 x) =
        ∫ x, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ ζ (x - d • e)) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · simp only [hφ1D]
      · intro x hx
        have : x - d • e ∉ K := fun h' => hx (hKdU' (hmemKd x h'))
        simp [hφ1D, hDζ0 _ this]
    have hr : ∫ x in U, inner ℝ (φ1 x) (g x) = ∫ x, R3 x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have : x - d • e ∉ K := fun h' => hx (hKdU' (hmemKd x h'))
      simp [hφ1, hζ0 _ this]
    have hl' : ∫ x, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ ζ (x - d • e)) = ∫ y, F1 y := by
      rw [← integral_add_right_eq_self _ (d • e)]
      simp [hF1]
    have hr' : ∫ x, R3 x = ∫ y, inner ℝ (ζ y) (g (y + d • e)) := by
      rw [← integral_add_right_eq_self _ (d • e)]
      simp [hR3]
    rw [hl, hr, hl', hr'] at h
    exact h
  have hR1R3 : ∫ y, inner ℝ (ζ y) (g (y + d • e)) = ∫ x, R3 x := by
    rw [← integral_add_right_eq_self R3 (d • e)]
    simp [hR3]
  -- (E3)
  have hE3 : ∫ y, (F1 y - F2 y) = ∫ x, inner ℝ (ζ x - ζ (x - d • e)) (g x) := by
    rw [integral_sub hF1i hF2i, hE1, hE2, hR1R3]
    have : ∫ x, inner ℝ (ζ x - ζ (x - d • e)) (g x) = ∫ x, (R2 x - R3 x) := by
      congr 1; funext x; simp [hR2, hR3, inner_sub_left]
    rw [this, integral_sub hR2i hR3i]
    ring
  -- FTC
  set I : Rn n → ℝ := fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Ψ)
    (fderiv ℝ u x + t • (fderiv ℝ u (x + d • e) - fderiv ℝ u x))
    (d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (fderiv ℝ ζ x) with hI
  set J : Rn n → ℝ := fun x => inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (fderiv ℝ ζ x e)
    with hJ
  have hFTC : ∀ y, F1 y - F2 y = d * I y := by
    intro y
    by_cases hy : y ∈ K
    · set Δ := fderiv ℝ u (y + d • e) - fderiv ℝ u y with hΔ
      have hderiv : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => fderiv ℝ Ψ (fderiv ℝ u y + t • Δ))
          (fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u y + t • Δ) Δ) t := by
        intro t _
        have hl : HasDerivAt (fun t : ℝ => fderiv ℝ u y + t • Δ) Δ t := by
          simpa using ((hasDerivAt_id t).smul_const Δ).const_add (fderiv ℝ u y)
        exact (hAd (fderiv ℝ u y + t • Δ)).hasFDerivAt.comp_hasDerivAt t hl
      have hint : IntervalIntegrable
          (fun t : ℝ => fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u y + t • Δ) Δ) volume 0 1 := by
        apply Continuous.intervalIntegrable
        exact (hBc.comp (by fun_prop)).clm_apply continuous_const
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      simp only [one_smul, zero_smul, add_zero] at hftc
      have hP1 : fderiv ℝ u y + Δ = fderiv ℝ u (y + d • e) := by simp [hΔ]
      rw [hP1] at hftc
      have happ := congrArg (fun L => L (fderiv ℝ ζ y)) hftc
      try simp only at happ
      rw [ContinuousLinearMap.intervalIntegral_apply hint] at happ
      simp only [hF1, hF2, hI]
      rw [← ContinuousLinearMap.sub_apply, ← happ, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    · simp [hF1, hF2, hI, hDζ0 y hy]
  have hIBP := Submission.dohr_eb_elc2_shift_ibp n ℓ U g ζ e d hU hg hζ hζc hsegK
  have hmain : ∫ x, I x = ∫ x, J x := by
    have h1 : ∫ y, (F1 y - F2 y) = d * ∫ x, I x := by
      rw [← integral_const_mul]; congr 1; funext y; exact hFTC y
    have h2 : d * ∫ x, I x = d * ∫ x, J x := by rw [← h1, hE3, hIBP]
    exact mul_left_cancel₀ hd h2
  have hIV : ∫ x in V, I x = ∫ x, I x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : x ∉ K := fun h' => hx (hKV h')
    simp [hI, hDζ0 x this]
  have hJV : ∫ x in V, J x = ∫ x, J x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : x ∉ K := fun h' => hx (hKV h')
    simp [hJ, hDζ0 x this]
  calc _ = ∫ x in V, I x := rfl
    _ = ∫ x in V, J x := by rw [hIV, hJV, hmain]
    _ = _ := rfl
```

## Key steps

1. integrands vanish outside K = tsupport zeta; reduce integrals over V to R^n
2. test the weak equation with zeta and with zeta(. - de); translate; subtract (all integrands continuous with compact support)
3. FTC for t -> DPsi(Du(y) + t Delta(y)) gives F1 - F2 = d I pointwise
4. sibling shift_ibp turns integral <zeta(x) - zeta(x - de), g(x)> into d integral J
5. cancel d != 0

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Contract.lean against <snapshot>/project/GMT/Ch05/Contract.lean (read the IsLocallyHolderCkα and IsHolderCkα definitions)`
- `rg -l 'lebesgue_number_lemma|integral_add_right_eq_self|toContinuousLinearMap|tsupport_comp_eq_preimage|IsLocallyHolderCkα|difference quotient|intervalIntegral_integral_swap|integral_integral_swap|maxSynthPendingDepth' <snapshot>/project`
- `rg -l -i 'lebesgue_number|integral_add_right_eq_self|difference quotient|Holder' .lake/packages/simongmt/Poincare; rg -n -i holder .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{FirstVariation,LpMeanCurvature}.lean`
- `grep -rn in <snapshot>/mathlib/Mathlib for: iteratedFDeriv_one_apply, norm_iteratedFDeriv_one, iteratedFDeriv_zero_eq_comp, iteratedFDeriv_succ_eq_comp_right, continuousMultilinearCurryFin1, contDiffOn_of_locally_contDiffOn, contDiffOn_zero, ContDiffOn.continuousOn_fderiv_of_isOpen, ContDiffOn.differentiableOn, ContDiff.fderiv_right, ContDiff.continuous_fderiv, lebesgue_number_lemma_of_metric, IsCompact.elim_finite_subcover, IsCompact.exists_bound_of_continuousOn, norm_image_sub_le_of_norm_fderiv_le (namespace Convex), norm_image_sub_le_of_norm_deriv_le_segment_01', integral_mul_right_eq_self (to_additive integral_add_right_eq_self), intervalIntegral.integral_eq_sub_of_hasDerivAt, integral_integral_swap, intervalIntegral_integral_swap, Measure.prod_restrict, IntegrableOn.of_forall_sdiff_eq_zero, ContinuousOn.integrableOn_compact, ContinuousOn.intervalIntegrable, ContinuousLinearMap.intervalIntegral_apply, ContinuousLinearMap.intervalIntegral_comp_comm, LinearMap.toContinuousLinearMap, setIntegral_congr_fun, setIntegral_eq_integral_of_forall_compl_eq_zero, fderiv_of_notMem_tsupport, fderiv_comp_sub, fderiv_comp_add_right, fderiv_const_smul, mulTSupport_comp_eq_preimage, HasCompactMulSupport.comp_isClosedEmbedding, HasCompactMulSupport.intro, Continuous.integrable_of_hasCompactSupport, integral_inner, intervalIntegral.norm_integral_le_of_norm_le_const, intervalIntegral.integral_mono_on, innerSL, EuclideanSpace.norm_single`
- `python3 scan of <run>/dag.json: lean_statements of the elliptic_bootstrap siblings; 'dohr_eb_elc2' name collisions; statements matching Lebesgue number / difference quotient / translat / bilinear form`
- `lake build GMT.Ch05.Submission in scratch /tmp/elc2-scratch-VvYZXQ/proj (Lean 4.35.0-rc3, shared lake-packages-25730c7c)`
- `lake env lean Checks/Children7.lean (seven child types in the replayed contract scope, generated with gmt-compare.py contract_scope)`
- `lake env lean Checks/Assembly.lean (frozen parent type from 6 child + 3 prerequisite axioms; #print axioms)`
- `lake env lean Checks/{C1feas,C2full,C3full,C4feas,C5feas,C6feas}.lean and Checks/EndToEnd.lean (complete child proofs; #print axioms)`
- `lake build of Submission.lean with the children under Submission.X; lake env lean Checks/NodeSolution_{0..7}.lean (gmt-compare.py child_modules output plus #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean match the snapshot contract. The project snapshot contains nothing on difference quotients, Lebesgue numbers, translated weak equations or bilinear-form averaging; its only relevant match is the definition of IsLocallyHolderCkα. The simongmt Holder matches are Hoelder's integral inequality and are irrelevant. Every Mathlib declaration cited in the child proofs exists at the pin, for example: integral_add_right_eq_self (to_additive of integral_mul_right_eq_self, Group/Integral.lean:101), intervalIntegral_integral_swap (Integral/Prod.lean:483), Measure.prod_restrict (Measure/Prod.lean:778), IntegrableOn.of_forall_sdiff_eq_zero (IntegrableOn.lean), ContinuousLinearMap.intervalIntegral_apply/_comp_comm (IntervalIntegral/Basic.lean:863/870), LinearMap.toContinuousLinearMap (Module/FiniteDimension.lean:307), lebesgue_number_lemma_of_metric (Pseudo/Lemmas.lean:120), contDiffOn_of_locally_contDiffOn (ContDiff/Defs.lean:586), fderiv_of_notMem_tsupport (FDeriv/Const.lean:375), fderiv_comp_sub (FDeriv/Add.lean:892), mulTSupport_comp_eq_preimage (Topology/Algebra/Support.lean:106), continuousMultilinearCurryFin1 (Multilinear/Curry.lean:510). Some names are deprecated (ContinuousLinearMap.sub_apply/smul_apply, push_neg) but still compile. No 'dohr_eb_elc2' name exists in dag.json and no existing DAG node duplicates a child. Lean checks: (1) all seven child types elaborate in the replayed contract scope; (2) the frozen parent type follows from 6 child + 3 prerequisite axioms without sorry; (3) all seven children have complete proofs using only propext, Classical.choice and Quot.sound, and with them under their Submission.X names each generated NodeSolution closes. Instance note: the bilinear-form type over L = Rn n →L[ℝ] Rn ℓ needs set_option maxSynthPendingDepth 3 (5 for D^3 Psi and for the FTC in L*).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/4503

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
