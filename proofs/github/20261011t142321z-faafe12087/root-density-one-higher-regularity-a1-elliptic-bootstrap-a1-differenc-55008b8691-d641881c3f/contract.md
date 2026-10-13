<!-- theorem-id: gmt-ch05/root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1.c1holder_limit-a1 -->

## Theorem `Submission.dohr_eb_dql_c1Holder_of_tendstoUniformlyOn`

Let n, l be natural numbers, iota a type with a filter l ≠ ⊥, F : iota -> (R^n -> R^l), G : R^n -> R^l, x0 ∈ R^n, and rho, alpha, M real with alpha > 0; let B := B_rho(x0) be the open ball, and write DF_i := fderiv ℝ (F i). Assume three eventual properties (each for l-eventually all i): F_i is differentiable at every point of B; ‖DF_i(x)‖ ≤ M for all x ∈ B; ‖DF_i(x) - DF_i(y)‖ ≤ M |x - y|^alpha for all x, y ∈ B. Assume also that F_i -> G uniformly on every compact K ⊆ B along l. Then G is C^1 on B, ‖DG(x)‖ ≤ M for all x ∈ B, and ‖DG(x) - DG(y)‖ ≤ M |x - y|^alpha for all x, y ∈ B, where DG := fderiv ℝ G.

Node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1.c1holder_limit-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2271

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3842

Decomposition children: None

## Lean problem

Declaration: `Submission.dohr_eb_dql_c1Holder_of_tendstoUniformlyOn`

```lean
∀ (n ℓ : ℕ) (ι : Type) (l : Filter ι), l.NeBot → ∀ (F : ι → Rn n → Rn ℓ) (G : Rn n → Rn ℓ) (x₀ : Rn n) (ρ α M : ℝ), 0 < α → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, DifferentiableAt ℝ (F i) x) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x‖ ≤ M) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x - fderiv ℝ (F i) y‖ ≤ M * ‖x - y‖ ^ α) → (∀ K : Set (Rn n), IsCompact K → K ⊆ ball x₀ ρ → TendstoUniformlyOn F G l K) → ContDiffOn ℝ 1 G (ball x₀ ρ) ∧ (∀ x ∈ ball x₀ ρ, ‖fderiv ℝ G x‖ ≤ M) ∧ ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ M * ‖x - y‖ ^ α
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

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1.c1holder_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4-7 of the parent proof of dohr_eb_difference_quotient_limit:
- the uniform Cauchy property of the derivatives, from the interpolation inequality;
- completeness of L(R^n, R^l);
- inheritance of the bounds by the limit;
- the theorem on uniform limits of derivatives.
It is stated for an abstract family F_i along a filter l ≠ ⊥ that converges uniformly on compact subsets of B. The parent applies it with i = d, l = 𝓝[≠] 0, F_d = g_d and G = D_e f.

Sibling lemma used: Submission.dohr_eb_dql_interpolation_fderiv_bound (key interpolation). Suppose 0 < t ≤ r, alpha > 0, L ≥ 0, h is differentiable at every point of B̄_{2r}(x), ‖Dh(y) - Dh(y')‖ ≤ L‖y - y'‖^alpha for y, y' ∈ B̄_{2r}(x), and ‖h(y)‖ ≤ S for y ∈ B̄_{2r}(x). Then ‖Dh(y)‖ ≤ 2S/t + L t^alpha for every y ∈ B̄_r(x).

Notation:
- B := ball(x0, rho), which is open and convex; B̄_s(z) := closedBall z s; DF_i := fderiv ℝ (F i).
- E := the set of i such that F_i is differentiable at every x ∈ B, ‖DF_i(x)‖ ≤ M for x ∈ B, and ‖DF_i(x) - DF_i(y)‖ ≤ M‖x - y‖^alpha for x, y ∈ B. E ∈ l, as the intersection of the three eventual hypotheses.
- V : R^n -> L(R^n, R^l) is defined by V(y) := limUnder l (fun i => DF_i(y)). This is a chosen limit, and it is the limit whenever one exists.

1. (Radii; sign of M.) For x ∈ B put r_x := (rho - dist(x, x0))/4 > 0. If dist(z, x) ≤ 2r_x, then dist(z, x0) ≤ dist(z, x) + dist(x, x0) ≤ (rho - dist(x, x0))/2 + dist(x, x0) < rho; so B̄_{2r_x}(x) ⊆ B. If x ∈ B then M ≥ 0: since l ≠ ⊥, E is non-empty, and for i ∈ E we have M ≥ ‖DF_i(x)‖ ≥ 0.

2. (Uniform Cauchy property.) Fix x ∈ B and r > 0 with B̄_{2r}(x) ⊆ B; by step 1, M ≥ 0. Let η > 0.
   (a) Since t^alpha -> 0 as t -> 0+ (alpha > 0), there is t with 0 < t ≤ r and 2M t^alpha < η/2. The set of such t belongs to 𝓝[>] 0, which is ≠ ⊥.
   (b) K := B̄_{2r}(x) is compact and K ⊆ B, so by hypothesis F_i -> G uniformly on K. Hence the set P of i ∈ E with ‖G(y) - F_i(y)‖ < ηt/8 for all y ∈ K belongs to l, and the pairs (i, j) ∈ P × P form a set of l ×ˢ l.
   (c) Fix such (i, j) and put h := F_i - F_j. Then:
      - h is differentiable at every point of K ⊆ B, with Dh(y) = DF_i(y) - DF_j(y) there (fderiv_sub);
      - for y, y' ∈ K: ‖Dh(y) - Dh(y')‖ = ‖(DF_i(y) - DF_i(y')) - (DF_j(y) - DF_j(y'))‖ ≤ M‖y - y'‖^alpha + M‖y - y'‖^alpha = 2M‖y - y'‖^alpha;
      - for y ∈ K: ‖h(y)‖ = ‖(G(y) - F_j(y)) - (G(y) - F_i(y))‖ ≤ ηt/8 + ηt/8 = ηt/4.
   (d) The interpolation lemma with L := 2M ≥ 0 and S := ηt/4 gives, for every y ∈ B̄_r(x),
      ‖DF_i(y) - DF_j(y)‖ ≤ 2(ηt/4)/t + 2M t^alpha = η/2 + 2M t^alpha < η.
   (e) As η > 0 was arbitrary, the family (DF_i) is uniformly Cauchy on B̄_r(x) along l (UniformCauchySeqOn; unfold it with Metric.mem_uniformity_dist and combine the eventualities with Filter.Eventually.prod_mk).

3. (Uniform limit.) L(R^n, R^l) is complete.
   (a) For y ∈ B̄_r(x), the image of l under i ↦ DF_i(y) is a Cauchy filter (UniformCauchySeqOn.cauchy_map, l ≠ ⊥). Hence it converges (cauchy_map_iff_exists_tendsto), and so DF_i(y) -> V(y) (tendsto_nhds_limUnder).
   (b) A uniformly Cauchy family that converges pointwise converges uniformly to its pointwise limit (UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto). So DF_i -> V uniformly on B̄_r(x) along l.
   (c) Apply this at each y ∈ B with r = r_y from step 1 (note y ∈ B̄_{r_y}(y)): DF_i(y) -> V(y) for every y ∈ B.

4. (Bounds for V and continuity.) Let y, y' ∈ B.
   (a) Eventually in l, ‖DF_i(y)‖ ≤ M and ‖DF_i(y) - DF_i(y')‖ ≤ M‖y - y'‖^alpha. By step 3 and continuity of the norm, DF_i(y) -> V(y) and DF_i(y) - DF_i(y') -> V(y) - V(y').
   (b) Since l ≠ ⊥, closed inequalities pass to the limit (le_of_tendsto): ‖V(y)‖ ≤ M and ‖V(y) - V(y')‖ ≤ M‖y - y'‖^alpha.
   (c) Hence V is continuous on B. For y, z ∈ B, 0 ≤ ‖V(z) - V(y)‖ ≤ M‖z - y‖^alpha, and M‖z - y‖^alpha -> M·0^alpha = 0 as z -> y (alpha > 0). So ‖V(z) - V(y)‖ -> 0 as z -> y within B (squeeze).

5. (Differentiability.) Fix x ∈ B and r := r_x. Apply the uniform-limit theorem for derivatives (hasFDerivAt_of_tendstoUniformlyOnFilter, filter l ≠ ⊥) to F_i, DF_i, G and V at x. Its three hypotheses hold:
   (a) DF_i -> V uniformly on B̄_r(x) (step 3). This set is a neighbourhood of x, so the convergence is uniform on the filter 𝓝 x (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, TendstoUniformlyOnFilter.mono_right).
   (b) For l ×ˢ 𝓝 x-eventually all (i, y), namely i ∈ E and y ∈ B (B is open and contains x), F_i has Fréchet derivative DF_i(y) at y (DifferentiableAt.hasFDerivAt).
   (c) For every y in the neighbourhood B of x, F_i(y) -> G(y) along l, because F_i -> G uniformly on the compact set {y} ⊆ B (TendstoUniformlyOn.tendsto_at).
   Therefore G has Fréchet derivative V(x) at x; in particular G is differentiable at x and fderiv ℝ G x = V(x). This holds for every x ∈ B.

6. (Conclusion.) G is differentiable at every point of the open set B, and fderiv ℝ G = V on B, which is continuous on B by step 4. Hence G is C^1 on B, via contDiffOn_succ_iff_fderiv_of_isOpen with 1 = 0 + 1:
   - G is differentiable on B;
   - the analyticity clause is vacuous since 0 ≠ ω;
   - ContDiffOn ℝ 0 (fderiv ℝ G) B is equivalent to ContinuousOn (contDiffOn_zero), which follows from the continuity of V by ContinuousOn.congr.
   Finally, for x, y ∈ B, ‖fderiv ℝ G x‖ = ‖V(x)‖ ≤ M and ‖fderiv ℝ G x - fderiv ℝ G y‖ = ‖V(x) - V(y)‖ ≤ M‖x - y‖^alpha by step 4. QED

Appendix (informative; checked Lean realization). The following proof of exactly the frozen type compiled without errors or warnings at the pinned toolchain (Lean 4.35.0-rc3, Mathlib 25730c7c). It was placed inside namespace GMT.Ch05 / namespace Submission with the contract's opens, after the sibling dohr_eb_dql_interpolation_fderiv_bound. #print axioms reports propext, Classical.choice, Quot.sound.

theorem dohr_eb_dql_c1Holder_of_tendstoUniformlyOn : ∀ (n ℓ : ℕ) (ι : Type) (l : Filter ι), l.NeBot → ∀ (F : ι → Rn n → Rn ℓ) (G : Rn n → Rn ℓ) (x₀ : Rn n) (ρ α M : ℝ), 0 < α → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, DifferentiableAt ℝ (F i) x) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x‖ ≤ M) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x - fderiv ℝ (F i) y‖ ≤ M * ‖x - y‖ ^ α) → (∀ K : Set (Rn n), IsCompact K → K ⊆ ball x₀ ρ → TendstoUniformlyOn F G l K) → ContDiffOn ℝ 1 G (ball x₀ ρ) ∧ (∀ x ∈ ball x₀ ρ, ‖fderiv ℝ G x‖ ≤ M) ∧ ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ M * ‖x - y‖ ^ α := by
  intro n ℓ ι l hl F G x₀ ρ α M hα hD hB hH hU
  have := hl
  have hE := hD.and (hB.and hH)
  set V : Rn n → (Rn n →L[ℝ] Rn ℓ) := fun y => limUnder l (fun i => fderiv ℝ (F i) y) with hVdef
  have hrad : ∀ x ∈ ball x₀ ρ, ∃ r > 0, closedBall x (2 * r) ⊆ ball x₀ ρ := by
    intro x hx
    rw [mem_ball] at hx
    refine ⟨(ρ - dist x x₀) / 4, by linarith, fun z hz => ?_⟩
    rw [mem_closedBall] at hz
    rw [mem_ball]
    calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
      _ < ρ := by linarith
  have hM : ∀ x ∈ ball x₀ ρ, 0 ≤ M := by
    intro x hx
    obtain ⟨i, hi⟩ := hB.exists
    exact (norm_nonneg _).trans (hi x hx)
  have hconv : ∀ x ∈ ball x₀ ρ, ∀ r > 0, closedBall x (2 * r) ⊆ ball x₀ ρ →
      TendstoUniformlyOn (fun i => fderiv ℝ (F i)) V l (closedBall x r) := by
    intro x hx r hr hsub
    have hM0 := hM x hx
    have hUC : UniformCauchySeqOn (fun i => fderiv ℝ (F i)) l (closedBall x r) := by
      intro u hu
      obtain ⟨η, hη, hηu⟩ := Metric.mem_uniformity_dist.1 hu
      have ht_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 2 * M * t ^ α < η / 2 := by
        have hc : Tendsto (fun t : ℝ => 2 * M * t ^ α) (𝓝 0) (𝓝 (2 * M * (0 : ℝ) ^ α)) :=
          ((continuousAt_id.rpow_const (Or.inr hα.le)).tendsto).const_mul _
        rw [Real.zero_rpow hα.ne', mul_zero] at hc
        exact nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds (by linarith)))
      have hIoc : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc 0 r := Ioc_mem_nhdsGT hr
      obtain ⟨t, ht1, ht2⟩ := (ht_ev.and hIoc).exists
      have htpos : 0 < t := ht2.1
      have htr : t ≤ r := ht2.2
      have hK : closedBall x (2 * r) ⊆ ball x₀ ρ := hsub
      have hTU := hU (closedBall x (2 * r)) (isCompact_closedBall x _) hK
      rw [Metric.tendstoUniformlyOn_iff] at hTU
      have hP := hE.and (hTU (η * t / 8) (by positivity))
      filter_upwards [hP.prod_mk hP] with ij hij y hy
      obtain ⟨⟨hDi, hBi, hHi⟩, hGi⟩ := hij.1
      obtain ⟨⟨hDj, hBj, hHj⟩, hGj⟩ := hij.2
      apply hηu
      rw [dist_eq_norm]
      have hyB : y ∈ closedBall x (2 * r) := closedBall_subset_closedBall (by linarith) hy
      set h : Rn n → Rn ℓ := fun z => F ij.1 z - F ij.2 z with hh
      have hdh : ∀ z ∈ closedBall x (2 * r), DifferentiableAt ℝ h z := fun z hz =>
        (hDi z (hK hz)).sub (hDj z (hK hz))
      have hfd : ∀ z ∈ closedBall x (2 * r),
          fderiv ℝ h z = fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.2) z := fun z hz =>
        fderiv_sub (hDi z (hK hz)) (hDj z (hK hz))
      have hbd := dohr_eb_dql_interpolation_fderiv_bound n ℓ h x r t α (2 * M) (η * t / 4)
        htpos htr hα (by linarith) hdh
        (fun z hz z' hz' => by
          rw [hfd z hz, hfd z' hz']
          calc ‖fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.2) z -
                (fderiv ℝ (F ij.1) z' - fderiv ℝ (F ij.2) z')‖
              = ‖(fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.1) z') -
                  (fderiv ℝ (F ij.2) z - fderiv ℝ (F ij.2) z')‖ := by congr 1; abel
            _ ≤ ‖fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.1) z'‖ +
                  ‖fderiv ℝ (F ij.2) z - fderiv ℝ (F ij.2) z'‖ := norm_sub_le _ _
            _ ≤ M * ‖z - z'‖ ^ α + M * ‖z - z'‖ ^ α :=
                add_le_add (hHi z (hK hz) z' (hK hz')) (hHj z (hK hz) z' (hK hz'))
            _ = 2 * M * ‖z - z'‖ ^ α := by ring)
        (fun z hz => by
          have h1 := hGi z hz
          have h2 := hGj z hz
          rw [dist_eq_norm] at h1 h2
          calc ‖h z‖ = ‖(G z - F ij.2 z) - (G z - F ij.1 z)‖ := by
                show ‖F ij.1 z - F ij.2 z‖ = _; congr 1; abel
            _ ≤ ‖G z - F ij.2 z‖ + ‖G z - F ij.1 z‖ := norm_sub_le _ _
            _ ≤ η * t / 4 := by linarith)
        y hy
      rw [hfd y hyB] at hbd
      calc ‖fderiv ℝ (F ij.1) y - fderiv ℝ (F ij.2) y‖ ≤ 2 * (η * t / 4) / t + 2 * M * t ^ α := hbd
        _ = η / 2 + 2 * M * t ^ α := by field_simp; ring
        _ < η := by linarith
    refine hUC.tendstoUniformlyOn_of_tendsto (fun y hy => ?_)
    have hc := hUC.cauchy_map hy
    obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hc
    exact tendsto_nhds_limUnder ⟨L, hL⟩
  have hpt : ∀ y ∈ ball x₀ ρ, Tendsto (fun i => fderiv ℝ (F i) y) l (𝓝 (V y)) := by
    intro y hy
    obtain ⟨r, hr, hsub⟩ := hrad y hy
    exact (hconv y hy r hr hsub).tendsto_at (mem_closedBall_self hr.le)
  have hG : ∀ x ∈ ball x₀ ρ, HasFDerivAt G (V x) x := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hrad x hx
    have hT := hconv x hx r hr hsub
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := l) (f := F) (f' := fun i => fderiv ℝ (F i)) ?_ ?_ ?_
    · exact (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.1 hT).mono_right
        (le_principal_iff.2 (closedBall_mem_nhds x hr))
    · filter_upwards [hD.prod_mk (isOpen_ball.mem_nhds hx)] with p hp
      exact (hp.1 p.2 hp.2).hasFDerivAt
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hU {y} isCompact_singleton (singleton_subset_iff.2 hy)).tendsto_at rfl
  have hfG : ∀ x ∈ ball x₀ ρ, fderiv ℝ G x = V x := fun x hx => (hG x hx).fderiv
  have hVb : ∀ x ∈ ball x₀ ρ, ‖V x‖ ≤ M := fun x hx =>
    le_of_tendsto (hpt x hx).norm (hB.mono fun i hi => hi x hx)
  have hVh : ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖V x - V y‖ ≤ M * ‖x - y‖ ^ α := fun x hx y hy =>
    le_of_tendsto ((hpt x hx).sub (hpt y hy)).norm (hH.mono fun i hi => hi x hx y hy)
  have hVc : ContinuousOn V (ball x₀ ρ) := by
    intro y hy
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun z => M * ‖z - y‖ ^ α) (𝓝 y) (𝓝 (M * ‖y - y‖ ^ α)) :=
      (((continuous_id.sub continuous_const).norm.continuousAt).rpow_const
        (Or.inr hα.le)).tendsto.const_mul M
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) ?_
      (hlim.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hVh z hz y hy
  refine ⟨?_, fun x hx => by rw [hfG x hx]; exact hVb x hx, fun x hx y hy => by
    rw [hfG x hx, hfG y hy]; exact hVh x hx y hy⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
  refine ⟨fun x hx => (hG x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hVc.congr hfG

## Key steps

1. each x in B has a radius r with closedBall(x, 2r) ⊆ B, and M ≥ 0 because the good set of indices is nonempty
2. the interpolation lemma applied to F_i - F_j (Hoelder constant 2M, sup bound eta t/4 from uniform convergence on closedBall(x, 2r)) makes DF_i uniformly Cauchy on closedBall(x, r)
3. completeness of L(R^n,R^l): DF_i -> V := limUnder uniformly on closedBall(x, r), hence pointwise on B
4. the limit V inherits the bound M and the Hoelder constant M, so V is continuous on B
5. hasFDerivAt_of_tendstoUniformlyOnFilter gives fderiv G = V on B; then ContDiffOn 1 follows from contDiffOn_succ_iff_fderiv_of_isOpen and contDiffOn_zero

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; cmp GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Contract.lean; git rev-parse HEAD`
- `grep -rn 'theorem hasFDerivAt_of_tendstoUniformlyOnFilter|theorem hasFDerivAt_of_tendstoLocallyUniformlyOn|theorem hasFDerivAt_of_tendstoUniformlyOn ' <snapshot>/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean (sed -n 290,440p)`
- `grep -rnE '(theorem|lemma|instance)[^:]*(exists_cthickening_subset_open|IsCompact.cthickening|closedBall_subset_cthickening|norm_image_sub_le_of_norm_hasFDerivWithin_le\'|norm_image_sub_le_of_norm_fderiv_le|tendstoUniformlyOn_iff|uniformContinuousOn_iff|contDiffOn_succ_iff_fderiv_of_isOpen|continuousOn_fderiv_of_isOpen|contDiffOn_zero|opNorm_le_bound|hasFDerivAt_comp_add_right|UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto|UniformCauchySeqOn.cauchy_map|cauchy_map_iff_exists_tendsto|tendsto_nhds_limUnder|Eventually.prod_mk|uniformCauchySeqOn_iff|IsCompact.uniformContinuousOn_of_continuous|le_of_tendsto)' <snapshot>/mathlib/Mathlib --include=*.lean`
- `grep -rn 'NeBot (𝓝\[≠\]' <snapshot>/mathlib/Mathlib --include=*.lean`
- `rg -l -i 'interpolation inequalit|Landau.Kolmogorov|kolmogorov inequality' <snapshot>/mathlib/Mathlib/Analysis; rg -l -i 'difference quotient' <snapshot>/mathlib/Mathlib`
- `rg -l -i 'interpolation|difference quotient|TendstoUniformlyOn' lake-packages-25730c7c/simongmt --glob '*.lean'; rg -l -i 'difference quotient|interpolation' <snapshot>/project/GMT`
- `python3 scan of dag.json lean_name values for dql/interpolation/diffQuot/c1Holder and of lean_statement values containing TendstoUniformlyOn/TendstoLocallyUniformlyOn/UniformCauchy/𝓝[≠] or fderiv with ^ α; grep -rl dohr_eb_dql nodes dag.json <snapshot>/project <snapshot>/mathlib/Mathlib`
- `python3 -I: contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') from verifier/gmt-compare.py (comparator replay scope)`
- `lake build GMT.Ch05.Submission in scratch copy /tmp/dql-decomp-WcgsEv/proj (Lean 4.35.0-rc3, shared lake-packages-25730c7c)`
- `lake env lean Checks/Assembly.lean (3 child types as axioms in namespace Submission, frozen parent proof, comparator-style exact Submission.X targets, #print axioms)`
- `lake env lean Checks/ChildA.lean; lake env lean Checks/ChildBC.lean; lake env lean Checks/Full.lean (children proved + parent; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Filter/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/DenselyOrdered.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`

PIN AND CONTRACT. The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd, which equals the workspace HEAD, and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean are byte-identical to the snapshot contract.

NO EXISTING LEMMA COVERS THE CHILDREN.
- Nothing at the pin gives an interpolation inequality: no interpolation/Landau-Kolmogorov match in Mathlib/Analysis.
- 'difference quotient' matches only Analysis/Calculus/UniformLimitsDeriv.lean. Its private difference_quotients_converge_uniformly belongs to the uniform-limit-of-derivatives theorem, not to difference quotients of a fixed C^1 map along a direction.
- No lemma states that C^{1,alpha} bounds are closed under locally uniform limits.
- The simongmt matches (Chapter01/Lusin.lean Egorov uniformization; Chapter06 current topologies) and the project GMT tree contain nothing relevant.

API THE CHILD PROOFS USE (lines at the pin):
- hasFDerivAt_of_tendstoUniformlyOnFilter [NeBot l] (UniformLimitsDeriv.lean:308; it allows eventually-differentiable families via l ×ˢ 𝓝 x)
- Convex.norm_image_sub_le_of_norm_fderiv_le' (MeanValue.lean:549)
- IsCompact.exists_cthickening_subset_open (Thickening.lean:426), IsCompact.cthickening (:283), closedBall_subset_cthickening (:537)
- IsCompact.uniformContinuousOn_of_continuous (HeineCantor.lean:49)
- contDiffOn_succ_iff_fderiv_of_isOpen (ContDiff/Defs.lean:891), ContDiffOn.continuousOn_fderiv_of_isOpen (:916), contDiffOn_zero (:618)
- hasFDerivAt_comp_add_right (FDeriv/Add.lean:847)
- UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto (UniformConvergence.lean:499), UniformCauchySeqOn.cauchy_map (:564)
- cauchy_map_iff_exists_tendsto (UniformSpace/Cauchy.lean:420), tendsto_nhds_limUnder (Topology/Basic.lean:245)
- Metric.tendstoUniformlyOn_iff (Pseudo/Basic.lean:142), Metric.uniformContinuousOn_iff (Pseudo/Defs.lean:759)
- Filter.Eventually.prod_mk (Order/Filter/Prod.lean:155), ContinuousLinearMap.opNorm_le_bound (Normed/Operator/Basic.lean:196), le_of_tendsto (Order/OrderClosed.lean:133)
- NeBot (𝓝[≠] x) instance (DenselyOrdered.lean:248)
Metric.uniformCauchySeqOn_iff exists only for atTop, so the child proof works from the definition of UniformCauchySeqOn. ContDiffOn.differentiableOn takes 1 ≠ 0.

NAMES. No dql/interpolation/diffQuot/c1Holder lean_name exists in dag.json (431 unique names). 'dohr_eb_dql' occurs nowhere in dag.json, the node directories or the snapshot, so the three proposed names are unreserved.

LEAN CHECKS (scratch build, replayed comparator scope).
- All three child types elaborate, and comparator-style targets close by exact Submission.X.
- With the children as axioms, the frozen parent type is proved; #print axioms lists propext, Classical.choice, Quot.sound, the c1Holder child and the diffQuot child.
- Each child type was also proved in Lean (C using B). The complete chain prints only propext, Classical.choice and Quot.sound, with no errors or warnings.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/4250

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
