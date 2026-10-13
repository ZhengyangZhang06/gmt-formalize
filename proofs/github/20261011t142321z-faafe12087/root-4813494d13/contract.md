<!-- theorem-id: gmt-ch05/root -->

## Theorem `GMT.Ch05.main_theorem`

# Simon GMT, Chapter 5: The Allard Regularity Theorem

Prove `GMT.Ch05.main_theorem`, stated in the frozen contract `GMT/Ch05/Contract.lean`, by completing `GMT/Ch05/Submission.lean` (initially a byte copy of the contract). The statement is the conjunction of the chapter's headline results; `GMT/Ch05/README.md` maps each conjunct to the book.

Source: Leon Simon, *Introduction to Geometric Measure Theory* (2014), Chapter 5, printed pages 103–130. Read-only copies for workers: `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt` and `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/simon-gmt.pdf` (printed page = PDF page − 7).

The pinned `simongmt` package (`Poincare.SimonGMT.*`) contains an earlier kernel-checked partial formalization of the book; its proofs may be reused as library lemmas where they apply. Do not rely on its definitions that the chapter README marks as unfaithful. Toolchain Lean v4.35.0-rc3, Mathlib 25730c7c. Every definition used by the statement must stay byte-identical; only standard axioms are allowed.

Node: `root`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: None (root)

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/112, https://github.com/ZhengyangZhang06/gmt-formalize/issues/113, https://github.com/ZhengyangZhang06/gmt-formalize/issues/114, https://github.com/ZhengyangZhang06/gmt-formalize/issues/115, https://github.com/ZhengyangZhang06/gmt-formalize/issues/116, https://github.com/ZhengyangZhang06/gmt-formalize/issues/118, https://github.com/ZhengyangZhang06/gmt-formalize/issues/119, https://github.com/ZhengyangZhang06/gmt-formalize/issues/121, https://github.com/ZhengyangZhang06/gmt-formalize/issues/123, https://github.com/ZhengyangZhang06/gmt-formalize/issues/124, https://github.com/ZhengyangZhang06/gmt-formalize/issues/126, https://github.com/ZhengyangZhang06/gmt-formalize/issues/128

## Lean problem

Declaration: `GMT.Ch05.main_theorem`

```lean
TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense
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

# Final proof of `GMT.Ch05.main_theorem` (root node)

Run `20261011T142321Z-faafe12087`, node `root`, issue
<https://github.com/ZhengyangZhang06/gmt-formalize/issues/4>.
Lean target `GMT/Ch05/Submission.lean`; frozen contract `GMT/Ch05/Contract.lean` at the frozen
commit `ea5607598f3133b40a13241f2e51517a8c6423cd` (Lean `v4.35.0-rc3`, Mathlib `25730c7c759d`,
`simongmt` package `2b3663083f3f`). Book: Simon, *Introduction to Geometric Measure Theory*,
Ch. 5, "The Allard Regularity Theorem" (`book/sources/chapter-05-source.txt`, sha256
`f2b3cadaebc7373e8a2768bdbd3b0cb0d3b357552bd9981b707c00a709ad9da8`; line numbers below refer to
this file). A public copy of the same text is the PDF
<https://web.stanford.edu/class/math285/ts-gmt>, which the prose audit also cites. I checked
its decompressed text streams: the title page reads "Introduction to Geometric Measure Theory,
Leon Simon, © Leon Simon 2014", and the table of contents lists §6 "Conical Approximation,
Extension of Allard's Th." on p. 124, as in the local source.

## 1. Statement

```lean
theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧
    LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧
    TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧
    ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧
    RegularSetOpenDense
```

Each conjunct is a closed proposition (`def … : Prop`) of the frozen contract, and
`main_theorem` has no hypotheses. The conjuncts formalize Simon Ch. 5:

* Lemma 2.1 (l. 193)
* Lemma 2.5 (l. 294)
* Lemma 2.6 (l. 377)
* Corollary 2.7 (l. 565)
* Lemma 3.1 (l. 592)
* Theorem 4.5 (l. 747)
* Theorem 5.2 (l. 1022)
* Remark 5.3 (l. 1035)
* Theorem 6.1 (l. 1157)
* the first and second assertions of Theorem 7.1 (l. 1312)
* Corollary 7.3 (l. 1378), with Definition 7.2 (l. 1368).

The contract's docstrings record the normalizations and errata that the frozen statements
already include. Examples are the mean-curvature term in the first inequality of 2.5, the
`ℝ^ℓ` target in 7.1, and the restriction of `Θ ≡ 1` to `spt V` in 7.1(ii). This proof uses the
statements exactly as frozen.

## 2. The Lean argument actually used

The proof of `main_theorem` (line 67601 of the final `Submission.lean`) is:

```lean
  exact ⟨Submission.tilt_excess_height_estimate,
    Submission.affine_approximation_lemma,
    Submission.lipschitz_approximation_lemma,
    Submission.lipschitz_graph_corollary,
    Submission.harmonic_approximation_lemma,
    Submission.tilt_excess_decay_theorem,
    Submission.allard_regularity_theorem,
    Submission.allard_regularity_any_radius,
    Submission.conical_approximation_theorem,
    Submission.density_one_regularity,
    Submission.density_one_higher_regularity,
    Submission.regular_set_open_dense⟩
```

`∧` is right-associative. So this twelve-component anonymous constructor elaborates to eleven
nested `And.intro`s, and component `i` must have type conjunct `i`. Each component is an
accepted child theorem whose declared type is exactly that conjunct. All names are in namespace
`GMT.Ch05`.

| # | Conjunct (book item) | Accepted child (declared type) | line |
|---|---|---|---|
| 1 | `TiltExcessHeightEstimate` (Lemma 2.1) | `Submission.tilt_excess_height_estimate : TiltExcessHeightEstimate` | 22528 |
| 2 | `AffineApproximationLemma` (Lemma 2.5) | `Submission.affine_approximation_lemma : AffineApproximationLemma` | 25151 |
| 3 | `LipschitzApproximationLemma` (Lemma 2.6) | `Submission.lipschitz_approximation_lemma : LipschitzApproximationLemma` | 29701 |
| 4 | `LipschitzGraphCorollary` (Cor. 2.7) | `Submission.lipschitz_graph_corollary : LipschitzGraphCorollary` | 31642 |
| 5 | `HarmonicApproximationLemma` (Lemma 3.1) | `Submission.harmonic_approximation_lemma : HarmonicApproximationLemma` | 29115 |
| 6 | `TiltExcessDecayTheorem` (Thm 4.5) | `Submission.tilt_excess_decay_theorem : TiltExcessDecayTheorem` | 29972 |
| 7 | `AllardRegularityTheorem` (Thm 5.2) | `Submission.allard_regularity_theorem : AllardRegularityTheorem` | 39913 |
| 8 | `AllardRegularityAnyRadius` (Rem. 5.3) | `Submission.allard_regularity_any_radius : AllardRegularityAnyRadius` | 51302 |
| 9 | `ConicalApproximationTheorem` (Thm 6.1) | `Submission.conical_approximation_theorem : ConicalApproximationTheorem` | 48197 |
| 10 | `DensityOneRegularity` (Thm 7.1, first assertion) | `Submission.density_one_regularity : DensityOneRegularity` | 67560 |
| 11 | `DensityOneHigherRegularity` (Thm 7.1, second assertion) | `Submission.density_one_higher_regularity : DensityOneHigherRegularity` | 64292 |
| 12 | `RegularSetOpenDense` (Cor. 7.3) | `Submission.regular_set_open_dense : RegularSetOpenDense` | 67536 |

The assembly uses no mathematics beyond `And.intro`. All of the mathematical content is in the
twelve accepted children, which are summarized in §4.

### Assumptions

* **No hypotheses beyond the frozen contract.** Lines 1–460 of `Contract.lean` (everything
  before `main_theorem`) appear byte-for-byte as lines 1–472 of `Submission.lean`. The only
  difference is twelve additional imports:
  * `Poincare.SimonGMT.Chapter02.WeightedArea` and `Poincare.SimonGMT.Chapter02.AreaLipschitz`
    from the pinned `simongmt` package;
  * ten Mathlib modules: `IntervalIntegral.AbsolutelyContinuousFun`,
    `Covering.BesicovitchVectorSpace`, `Covering.Differentiation`, `Covering.DensityTheorem`,
    `Function.Jacobian`, `Constructions.Polish.Basic`, `Calculus.FDeriv.Measurable`,
    `Measure.Lebesgue.VolumeOfBalls`, `BumpFunction.Normed` and `BumpFunction.InnerProduct`.

  I checked that these imports do not change how any frozen constant elaborates. I elaborated
  two scratch files with the pinned toolchain:
  * `Contract.lean` itself;
  * lines 1–472 of `Submission.lean`, followed by the contract's `main_theorem := by sorry`
    stub.

  For every constant in `GMT.Ch05` that each file adds, I compared the structural hashes
  (`Expr.hash`) of its type and value, and its universe parameters. All 80 constants are
  identical. They include all definitions, the structure `RectifiableVarifold` with its
  projections, the auxiliary declarations, and the statement of `main_theorem`. The comparator
  independently checks that every constant used by the statement is the same in `Contract` and
  `Submission` (§8).
* **Axioms:** only `propext`, `Classical.choice` and `Quot.sound` (§8).
* **No proof shortcuts:** the file contains no `sorry`, `admit`, `axiom`, `native_decide`,
  `implemented_by`, `extern`, `unsafe` or `opaque` declaration. No definition or assumption is
  changed.
* **Build settings (not mathematics).** All accepted declarations except
  `density_one_regularity` sit inside an
  `elaborate_without_info_trees … end_elaborate_without_info_trees` block. Lines 473–488 define
  the command and lines 493–67551 use it. `density_one_regularity` (lines 67553–67599) and
  `main_theorem` follow the block.
  * This command elaborates the enclosed commands as at top level, but it switches
    info-tree recording off (`withEnableInfoTree false`) and sets `Elab.async` to false.
  * It was introduced in the accepted checkpoint `14b7adf1a28b` of node `root.tilt_excess_decay-a1`
    (PR #5200), because the verification sandbox ran out of memory while Lean kept the info tree
    of every command.
  * Info trees are editor metadata only. Every enclosed declaration is still elaborated and
    added to the environment through the kernel.

  The file also has these settings:
  * `set_option linter.unusedTactic false` and `set_option linter.unreachableTactic false`.
    These two linters read info trees, so without info trees they would flag every tactic.
  * Local `set_option maxHeartbeats …` and `set_option maxSynthPendingDepth 3` on some
    declarations.
  * The core tactic `as_aux_lemma` inside the proof of Theorem 6.1, which stores finished
    subproofs as auxiliary theorems.

  None of these settings affects what the kernel checks. `main_theorem` is elaborated after the
  block, at top level. Its settings are the defaults except for the two linter options above,
  which stay off for the rest of the file.

## 3. This candidate: integration repair

**Rejected base.** The controller built this branch's base `14edad132e7d` by overlaying the
accepted child checkpoints (merges plus "re-merge declarations" commits). The comparator
rejected it with

```
GMT/Ch05/Submission.lean:18198:8: error:
  `GMT.Ch05.Submission.lipts_rectifiable_tangent_chart_cover` has already been declared
```

This is the only error (log line 495). The full log is `comparator.log` in the evidence
directory `cluster-state/verification/results/hoa63/20261013T133825Z-ch05-root-ds67xlr5`.
The first version of this document cited the run's `nodes/root/comparator-v1.log` for this
log. That file now holds the controller's later passing run on `dc91aaf9` (§8), so the
evidence directory is the record of the rejection.

**Repair.** Commit `26012c4ae4071cbf92436dec796a678f939b243e` changes only the Lean target
(2 insertions, 32 deletions):

1. **Removed the repeated chart cover.** I deleted lines 18190–18219 of `14edad13`, which hold
   the second copy of `lipts_rectifiable_tangent_chart_cover` (docstring and proof) and a
   repeated section note `/-! ### lip_approx_tangent_structure … -/`. This copy is identical to
   the first copy at lines 11153–11181 apart from one blank line. The first copy stays at line
   11161, before its user `lip_approx_tangent_structure` (line 12081). The controller's
   deduplication commit `59a90554` had already removed a third copy of the same block in the
   same way.
2. **Restored two accepted names.** In their accepted checkpoints, two declarations are written
   at the top level of namespace `GMT.Ch05` as `theorem Submission.X`:
   * `tdo_ods_integrableOn_norm_deriv`, checkpoint `07483dd7d591`, node
     `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1.ftc_bound-a1.deriv_norm_integrable-a1`;
   * `dohr_eb_elc2_averaged_hessian`, checkpoint `dbd206dd8e88`, node
     `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.averaged_hessian-a1`.

   The overlay placed them inside `namespace Submission` blocks (now lines 15237–15955 and
   56759–60682), so they were declared as `GMT.Ch05.Submission.Submission.X`. The two
   `linter.dupNamespace` warnings in the rejected run's `comparator.log` show this. I renamed
   them to `theorem tdo_ods_integrableOn_norm_deriv` (line 15790) and
   `theorem dohr_eb_elc2_averaged_hessian` (line 57501), which gives them their accepted names
   `GMT.Ch05.Submission.X` again.

   Each name has one call site, written `Submission.X …`: line 15908, and line 63840 in
   `dohr_eb_el_c2alpha_regularity`. Both call sites are inside `namespace GMT.Ch05.Submission`,
   where `Submission.X` resolves to `GMT.Ch05.Submission.X`.

No statement and no proof body was changed.

**Checks on the committed file.**

* After the contract preamble there are 562 declarations, all theorems:
  * `main_theorem`;
  * the 541 accepted DAG theorems (every accepted node below the root);
  * 20 helpers `liptsp_*` (lines 11183–12018). These belong to the accepted checkpoint
    `6c95c30c9b06` of node `root.lipschitz_approximation-a1.tangent_structure-a1` (PR #2840),
    whose `lip_approx_tangent_structure` uses them. All 20 are identical to that checkpoint, and
    this repair added none of them.
* Every accepted `lean_name` occurs exactly once, as `GMT.Ch05.Submission.<lean_name>`. There
  are no duplicate declarations and no `Submission.Submission.*` names. There is no repeated
  placeholder scaffold: `main_theorem` occurs once, the contract's `:= by sorry` stub was
  replaced, and there is no `sorry` anywhere.
* Each of the 541 accepted declarations, from its `theorem` line to the end of its proof, is
  textually identical to the declaration in its own accepted candidate commit (`candidate_commit`
  in `dag.json`). The comparison ignores trailing whitespace. It also treats
  `theorem Submission.X` at top level as equal to `theorem X` inside `namespace Submission`,
  since both declare `GMT.Ch05.Submission.X`.

### Revisions of this document (prose only)

The first version of this document was committed in `dc91aaf9`. It has been revised twice.
Neither revision changes `GMT/Ch05/Submission.lean` or any other comparator input; these are
byte-identical to `26012c4a`.

**First revision (`20f58c4d`).** The controller's prose audit
`nodes/root/publication-prose-audit-v1.json` reviewed exactly the first version: its
`proof_blob` `e3d4f77233cd` is the blob of this file in `dc91aaf9`. It did not accept that
version. Its two issues both concern the conical-approximation exposition in §4.9, and ask to:

1. state a support condition that makes the field `X(x) = x ∫_1^{1/τ} s^{n−1} g(sx) ds`
   admissible in `U`, and check it for the cutoffs used;
2. keep the dimensional constant in the bound for `∫_{B_1 ∖ B_λ} |x|^{1−n} |H| dμ`, and define
   the three annular integrals.

The first revision rewrote §4.9 to follow the Lean proof step by step:

* Step 2 states the hypothesis `tsupport g ⊆ B_β(0) ⊆ U` of `conical_P1` and explains why it is
  needed.
* Steps 4 and 8 check it for the radial cutoffs (`β = 1 + ε`) and for the conical test
  functions (`β = b ≤ 1`).
* Step 7 defines `I_⊥`, `I_0` and `I_H` and gives the bounds proved in Lean:
  `(ω_n + 3) δL`, `(Λ + 3)(1 + nL)` and `δ(1 + (n − 1)L) ≤ nδL`.
* Step 9 absorbs these constants into the final `C`.

It also made these changes:

* §6 and §7 list the Mathlib declarations that §4.9 now names.
* The header cites the public copy of the book.
* §3 points to the evidence directory for the rejected run's log.
* §8 describes the commit.

**Second revision (this commit).** The audit `nodes/root/publication-prose-audit-v2.json`
reviewed exactly the first revision: its `proof_blob` `ee8bae68875e` is the blob of this file
in `20f58c4d`. It found that the previous objections were addressed. It did not accept that
version, because of one remaining issue in step 12 of §4.9. That step claimed that all sets
involved lie in `B_1`. This is false for `B_{(1+d)ρ}(ξ)`: at the allowed endpoint `ρ = θ`,
`|ξ| + (1+d)ρ = 1 + dθ > 1`, and the finiteness of the mass of this ball is not established.
The audit asks to keep `A = B_{(1+d)ρ}(ξ) ∩ B_1` through the limit and the conversion to
`[0, ∞]`, and to enlarge `A` to the ball only by monotonicity in `[0, ∞]`.

The Lean proof already argues exactly this way (`hconv2`, line 50697). Only its description was
wrong. This revision corrects the description:

* The notation and step 0(c) of §4.9 say when a mass is used as a real number, and that the
  hypotheses give no bound for the mass of a set not contained in `U`.
* Step 6 introduces `A` and the two real inequalities (R1) and (R2) between masses of subsets
  of `B_1`, and proves them in the trivial case.
* Step 11 shows `g_k ≤ 1_A` and the domination by `1_{B_1}`, and ends with (R2) for `μ(A)`, not
  for the mass of the ball. Step 10 ends with (R1).
* Step 12 converts (R1) and (R2) to `[0, ∞]`, and enlarges `μ(A)` to `μ(B_{(1+d)ρ}(ξ))` only
  there, by monotonicity. It also explains why the ball's mass is never used as a real number.
* The claim of §4.9 now says that the inequalities hold in `[0, ∞]`. Its introduction gives
  the Lean locations of `hμsub`, `hconv`, `hconv2`, `hfirst` and `hsecond`.
* Step 8 no longer lists `κ ≥ 0` among the hypotheses of `conical_P4`. The Lean proof derives
  it from `|φ′| ≤ κ/ρ`.
* The notation describes `K_S` as the Lean proof obtains it: some bound `K_S ≥ 0` for `|S′|`,
  not necessarily `sup |S′|`.
* §6 and §7 add the Mathlib declarations that steps 0, 6, 11 and 12 now name (the
  `ENNReal.ofReal`/`toReal` conversion lemmas, `measure_mono` and `measure_diff_null`), with
  their locations in the pinned snapshot.
* §8 lists the comparator runs on the revisions.

The audit records and the root's historical outline and plan are unchanged.

## 4. Proof of each conjunct (the accepted children)

Each child has the following:

* its own reviewed natural-language proof, in the run's
  `nodes/root-<child>-a1/parent-supplied-natural-proof.md`, taken from the accepted
  decomposition `nodes/root/decomposition-v2.json`;
* its own tree of accepted descendants (541 accepted nodes in total, depth ≤ 6);
* a kernel-checked Lean proof that passed the comparator for its frozen type.

The summaries below describe the routes of the Lean proofs, as documented in the declarations'
docstrings and the accepted decomposition. Departures from the printed proofs are stated. "Uses"
lists the sibling conjuncts that the Lean proof references directly.

### 4.1 Lemma 2.1 — `tilt_excess_height_estimate` (issue #112, PR #3357, checkpoint `ed867b35a45e`)

**Claim.** `E(ξ, ρ/2, T) ≤ C ρ^{-n} ∫_{B_ρ(ξ)} (dist(x−ξ, T)/ρ)² dμ + C ρ^{2−n} ∫_{B_ρ(ξ)} |H|² dμ`
for every `n`-plane `T` with `B_ρ(ξ) ⊆ U`, with `C = 146·2^{n+1}`.

**Proof.**
1. If `∫|H|² = ∞` there is nothing to prove.
2. Otherwise, test the first-variation identity with the `C¹` field `X = ζ² p_{T⊥}(x − ξ)`. Here
   `ζ` is a cutoff that equals `1` on `B_{ρ/2}(ξ)` and vanishes off `B̆_ρ(ξ)`.
3. Wherever `T_x M` exists,
   `div_M X = ζ²|p_x − p_T|²/2 + 2ζ Dζ((p_x − p_T) p_{T⊥}(x − ξ))`
   (`divM_height_test_field_eq`).
4. Young's inequality absorbs the cross term, and
   `|x′||H| ≤ ρ^{-2}|x′|²/2 + ρ²|H|²/2` handles the curvature term.

**Uses:** none.

### 4.2 Lemma 2.5 — `affine_approximation_lemma` (issue #113, PR #4183, checkpoint `bee03434612e`)

**Claim.** This is the corrected statement of the contract.

**Proof.**
1. **Corrected monotonicity.** Monotonicity is used with the constant of Ch. 4, 4.2 read
   correctly: `κ = (p−n)/(4p)`, i.e. `Λ = 4pδ/(p−n)`. This gives a mass bound for every
   `δ ≤ 1/4`, and the pinched density bounds 2.4 for `δ` below a threshold depending only on
   `n` and `p`.
2. **First inequality, for every `n`-plane.** It follows from an `L¹` form of 2.1 ("Lemma A",
   `aal_l1_tilt_height`) together with Hölder's inequality (`aal_tilt_height_curvature_bound`).
3. **Large `δ`.** For `δ > δ₁`, the plane `ℝⁿ × {0}` has height `≤ σ`, and
   `1 ≤ δ₁^{-1/(2n+2)} δ^{1/(2n+2)}`.
4. **Small `δ`.** For `δ ≤ δ₁`, combine three ingredients: the `O(δ)` conical excess at each
   point, a maximal disjoint family of radius `δ^α σ/2` (`aal_packing_finite_net`), and a
   Chebyshev choice of a point `x₀` where `T_{x₀}M` exists. Together they give `T = T_{x₀}M`
   with height `≤ C δ^{1/(2n+2)} σ`, where `α = 1/(2n+2)` (`aal_height_bound_small_delta`).

**Uses:** none.

### 4.3 Lemma 2.6 — `lipschitz_approximation_lemma` (issue #114, PR #4438, checkpoint `f15e34061dc3`)

**Case 1.** The tilt of `T₀ = q(ℝⁿ × {0})` on `B_{σ₀}(0)` exceeds `β²L²σ₀ⁿ`. Then `f = 0`
works, by the pinched density bounds and the graph-measure bound.

**Case 2.** Otherwise:
1. The good set `G` is a Lipschitz graph over `T₀` with constant `2C₈βL`
   (`lip_approx_good_set_flat`, which uses Lemma 2.5).
2. `f` is a bounded Lipschitz extension of it (`lip_approx_bounded_extension`). Each coordinate
   is extended by McShane's construction (Mathlib `LipschitzOnWith.extend_real`), and the result
   is composed with the radial retraction onto `B_{R₀}(0)`, which is `1`-Lipschitz. This
   retraction replaces the book's componentwise truncation in (7).
3. The two error terms are bounded by a five-times covering estimate
   (`lip_approx_good_set_complement`) and by the monotonicity "hole" estimate
   (`lip_approx_graph_hole_measure`).

**Uses:** 2.5.

### 4.4 Corollary 2.7 — `lipschitz_graph_corollary` (issue #115, PR #4360, checkpoint `3f540aeba8ce`)

1. **Height cone.** `lgc_height_cone` applies 2.5 with `τ = βL`.
2. **Graph and extension.** `lgc_cone_graph_extension` shows that `spt V ∩ B_{σ₀/2}(0)` is a
   small-Lipschitz graph over `T₀`, and extends it to `f` with `Lip f ≤ L` and the sup bound.
3. **Forward inclusion.** This is immediate.
4. **Reverse inclusion.** Take a graph point over `Bⁿ_{σ₀/4}(0)` that is off `spt V`. Move it
   along the graph (intermediate value theorem) to a point at distance `d ∈ (0, σ₀/64]` from
   `spt V`. There, the hole estimate `lgc_hole_estimate` contradicts the tilt hypothesis on
   `B_{5d/2}(y)`.

**Uses:** 2.5.

### 4.5 Lemma 3.1 — `harmonic_approximation_lemma` (issue #116, PR #3958, checkpoint `6dd3d3a30cac`)

This follows the book's compactness argument.
1. Take a counterexample sequence for `δ = 1/(k+1)`, normalized by its means over `B`.
2. Three tools give a subsequence converging to some `w ∈ W^{1,2}(B)` with weak gradient `g`
   and `∫_B |g|² ≤ 1`:
   * the Poincaré inequality on balls (`w12_ball_poincare_inequality`);
   * Rellich's theorem (`w12_ball_rellich_compactness`);
   * weak compactness of `L²(B; ℝⁿ)`.
3. The defect bound `|∫ g_k · ∇ζ| ≤ sup|∇ζ|/(k+1)` makes `w` weakly harmonic.
4. Weyl's lemma (`w12_ball_weyl_lemma`) gives a harmonic `u₀` with `u₀ = w` a.e.
5. Then `u₀` plus the mean contradicts the choice of the sequence.

**Uses:** none.

### 4.6 Theorem 4.5 — `tilt_excess_decay_theorem` (issue #118, PR #5200, checkpoint `14b7adf1a28b`)

1. **Re-centre at `ξ`.** Use `ted_translate_varifold` with `δ″ = C_P δ`, where `C_P` comes from
   the mass bound of `ted_allard_density_bounds`, and with `ρ″ = σ/δ″`.
2. **Decay at the origin.** `ted_decay_at_origin` with contraction `η` runs through these steps:
   * reduce to `E(0, σ, T) ≤ Cδ^{1/(n+1)}`;
   * apply the Lipschitz approximation 2.6 with `L = 1`;
   * derive the weak equation for `f`, localized to `B_{σ/2}(0)`. Since `Lip f ≤ 1` is an
     operator-norm bound, `|Df|²_HS ≤ n` and `1 ≤ J_F ≤ 2^{n/2}`;
   * apply the harmonic approximation 3.1;
   * obtain affine approximation from the mean-value estimates 3.2–3.4;
   * bound the tilt by the height: by 2.1 if `p ≥ 2`, and by Lemma A plus a one-dimensional sup
     bound if `n = 1 < p < 2`.
3. **Choose `η`.** Pick `η` with `Cη² ≤ η^{2(1−n/p)}`. The curvature term scales as
   `K(ξ, ησ) ≤ η^{1−n/p} K(ξ, σ)`.

**Uses:** 2.1, 2.5, 2.6, 3.1.

### 4.7 Theorem 5.2 — `allard_regularity_theorem` (issue #119, PR #5480, checkpoint `4b5746e68ccd`)

1. Fix `δ₀(n, ℓ, p)` and `γ = δ₀/8192`.
2. Lemma 2.5 at `(0, 2δ₀ρ)` and the iteration of 4.5 give planes `S(ξ)` with tilt decay.
3. Corollary 2.7, with `T₀ = S(0)` and `L = min{L_c, L₀/√n}`, makes `spt V` a Lipschitz graph
   over `B_{δ₀ρ/4}(0)`. The factor `1/√n` turns the operator-norm bound into the
   Hilbert–Schmidt bound that the Campanato step needs.
4. The Campanato estimate (`allard52_graph_campanato`, `allard52_campanato_*`) makes the graph
   `C^{1,1−n/p}` with `Df(0) = 0`.
5. The conical excess at `0` bounds the height by `Cδ^{1/(2n+2)}|x|`, via monotonicity with the
   true `δ` and radial integration.
6. Lemma A then bounds the tilt at a fixed scale by `Cδ^{1/(n+1)}`. Restarting the decay
   iteration there gives the `C^{1,1−n/p}` estimate with rate `δ^{1/(2n+2)}`.

**Uses:** 2.5, 2.7, 4.5.

### 4.8 Remark 5.3 — `allard_regularity_any_radius` (issue #121, PR #5942, checkpoint `96627165d312`)

1. Theorem 5.2 at `(0, ρ)` gives `q₀, u₀`. With the mean value inequality this yields the
   thin-cone hypothesis of `any_radius_cone` around `T₀`.
2. Two results give local graphs of slope `≤ 1/24` at a fixed scale around every
   `y ∈ spt V ∩ B_{(1+3γ)ρ/4}(0)`:
   * pinching (`any_radius_pinching`), which applies Theorem 6.1 after dilation;
   * Theorem 5.2 applied to the translates `V − y` (`any_radius_rescaled_varifold`).
3. `any_radius_patching` glues these into a single graph over `T₀` on `B̆_{(1+7γ)ρ/8}(0)`.
4. `any_radius_graph_rate` gives the height, slope and Hölder bounds on `B_{γρ}(0)`, through
   conical excess, Lemma A, the 4.5 iteration and Campanato.

The sibling theorems enter as explicit hypotheses:
* `any_radius_pinching`, `any_radius_cone` and `any_radius_graph_rate` each take
  `ConicalApproximationTheorem` as a hypothesis;
* `any_radius_graph_rate` also takes `TiltExcessDecayTheorem`.

The proof of 5.3 supplies `Submission.conical_approximation_theorem` and
`Submission.tilt_excess_decay_theorem` for these hypotheses (lines 51420, 51447, 51450–51451).
It calls `Submission.allard_regularity_theorem` directly.

**Uses:** 5.2, 6.1, 4.5.

### 4.9 Theorem 6.1 — `conical_approximation_theorem` (issue #123, PR #3057, checkpoint `0f113e83c542`)

This section was rewritten in the first revision of this document and corrected in the second
(§3). It follows the Lean proof: the local lemmas `conical_P1` (step 2 below, line 48199),
`conical_P3` (step 3, line 48466), `conical_P2` (step 4, line 48686), `conical_P4` (step 8,
line 49255), the tangent-plane lemma `lemmaT` (step 1, line 49747) and the final assembly
(steps 0 and 5–12, from line 50462). In the assembly, `hμsub` (line 50591) is the finiteness
statement of 0(c), and `hconv` and `hconv2` (lines 50690 and 50697) are the two conversions of
step 12. The trivial case starts at line 50723 (`by_cases htriv`), (R1) for `dL ≤ 1` is
`hfirst` (line 50984), and (R2) for `dL ≤ 1` is `hsecond` (line 51287).

**Claim.** Fix `n ≥ 1`, `ℓ` and `Λ > 0`. Let `λ, θ, δ ∈ (0, 1/4)` and `|ξ| = 1 − θ`. Let
`U ⊇ B_1(0)` be open. Let `V` have generalized mean curvature `H` in `U`, and write
`μ = μ_V`. Assume `μ(B_1) ≤ Λ` and

* (H) `|μ(B_1)/ω_n − μ(B_λ)/(ω_n λⁿ)| + r^{1−n} ∫_{B_r} |H| dμ ≤ δ` for every `r ∈ [λ, 1]`.

Then for all `ρ ∈ (0, θ]` and `τ ∈ [2λ, 1]`, in `[0, ∞]`:

* `μ(B_{(1−d)ρ}(ξ)) ≤ τ^{-n} μ(B_{τρ}(τξ)) + C d L`;
* `τ^{-n} μ(B_{τρ}(τξ)) ≤ μ(B_{(1+d)ρ}(ξ)) + C d L`.

Here `d = δ^{1/4}` and `L = |log λ|`. The constant `C` is given in step 9 and depends only on
`n` and `Λ`. All balls are closed, `B_r = B_r(0)`, and `ω_n = unitBallVolume n`.

**Notation.**

* `μ` takes values in `[0, ∞]`. In steps 0–11, every mass used as a real number is `μ(S)` for a
  set `S ⊆ B_1`. Such a mass is finite by 0(c), and `μ(S)` then denotes the real number
  `(V.weight S).toReal`. Step 12 converts the resulting real inequalities to `[0, ∞]`.
* `p_x = p_{T_x M}` (`V.tangentProj x`) and `x^⊥ = x − p_x x`.
* For every `x`, `p_x` is either `0` or an orthogonal projection, by the definition of
  `tangentProj`. Hence, for all `x`:
  * (i) `|x^⊥| ≤ |x|`;
  * (ii) `⟨x, x^⊥⟩ = |x^⊥|²`.
* `S` is Mathlib's smooth step `Real.smoothTransition`. It is `C^∞` and nondecreasing, takes
  values in `[0, 1]`, and has `S = 0` on `(−∞, 0]` and `S = 1` on `[1, ∞)`.
* `K_S ≥ 0` is a bound for `S′`: `|S′(t)| ≤ K_S` for all `t`. It exists because `S′` is
  continuous and vanishes outside `[0, 1]`. The Lean proof takes `K_S = max(K, 0)`, where `K`
  bounds `|S′|` on `[0, 1]`; any such bound works below.

0. **Consequences of the hypotheses.**
   * (a) The first summand in (H) is nonnegative. So `∫_{B_t} |H| dμ ≤ δ t^{n−1}` for every
     `t ∈ [λ, 1]`.
   * (b) Take `r = 1` in (H) and multiply by `ω_n`: `|μ(B_1) − λ^{-n} μ(B_λ)| ≤ ω_n δ`.
   * (c) `μ(B_r) < ∞` for `r ≤ 1`, because the multiplicity `θ_V` of `V = v(M, θ_V)` is
     integrable on compact subsets of `U` (`V.integrableOn_mult`). Hence `μ(S) ≤ μ(B_1) < ∞`
     for every `S ⊆ B_1` (`hμsub`). The hypothesis `μ(B_1) ≤ ofReal Λ` gives the real bound
     `μ(B_1) ≤ Λ`, since `Λ > 0` (`ENNReal.toReal_le_of_le_ofReal`, `hΛ1`). For real masses
     of subsets of `B_1`, `S ⊆ S′` implies `μ(S) ≤ μ(S′)` (`ENNReal.toReal_mono`). The
     hypotheses bound `μ` only on compact subsets of `U`. They give no bound for the mass of a
     set that is not contained in `U`, such as a ball reaching outside `U`. Also, `H` is
     `μ`-integrable on every compact subset of `U`; this is part of
     `HasGeneralizedMeanCurvature`.
   * (d) `L = log(1/λ) > log 4 > 1`.
   * (e) Geometry:
     * `|ξ| + ρ ≤ (1 − θ) + θ = 1`, so `B_ρ(ξ) ⊆ B_1`;
     * `|ξ| − ρ ≥ 1 − 2θ > 1/2`;
     * `B_{τρ}(τξ) ⊆ B_τ`;
     * `λ ≤ τ/2`.
1. **Tangent planes (Simon Ch. 3, 1.9).** `lemmaT` proves two facts:
   * `μ`-a.e., `p_x` is the orthogonal projection onto an `n`-plane (the weighted approximate
     tangent space);
   * `x ↦ p_x` is `μ`-a.e. strongly measurable.

   It uses these accepted lemmas, all declared before this theorem (lines 8241–14812):
   * `aetp_lusin_compact_exhaustion`, `aetp_upper_density_zero_ae`,
     `aetp_starProjection_range_continuousOn` and `aetp_weightedTangent_of_lusin_compact`,
     from the subtree of `tilt_excess_height_estimate`;
   * `rsod_blowUp_setIntegral_eq`, from the subtree of `regular_set_open_dense`.

   It also uses the `simongmt` results listed in §6.
2. **(P1) First variation of the radial field `X(x) = F(x) x`.**

   *Hypotheses.* `g ∈ C¹(ℝ^{n+ℓ})`, a radius `β` with `tsupport g ⊆ B_β(0)` and
   `B_β(0) ⊆ U`, and `τ ∈ (0, 1]`. Put `F(x) = ∫_1^{1/τ} s^{n−1} g(sx) ds`.

   *Conclusion.* Put `J(x) = ∫_1^{1/τ} sⁿ Dg(sx)(x^⊥) ds`. Then
   `∫ (τ^{-n} g(x/τ) − g(x)) dμ = ∫ J dμ − ∫ F(x) ⟨x, H(x)⟩ dμ`.

   *Proof.*
   * **Admissibility.** Let `|x| > β`. For every `s ∈ [1, 1/τ]`, `|sx| ≥ |x| > β`, so
     `g(sx) = 0` and `Dg(sx) = 0`. Hence `F` and `DF` vanish there, and
     `tsupport X ⊆ B_β(0) ⊆ U`. In particular `X` has compact support.
     Differentiation under the integral sign gives `F ∈ C¹` with
     `DF(x) = ∫_1^{1/τ} sⁿ Dg(sx) ds`; the `x`-derivative `sⁿ Dg(sx)` of the integrand is
     bounded by `τ^{-n} sup|Dg|`. So `X ∈ C¹_c` with `tsupport X ⊆ U`, and `X` is a valid test
     field in the definition of generalized mean curvature.

     The support hypothesis is needed. `X` vanishes outside the radial contractions
     `{y/s : g(y) ≠ 0, s ∈ [1, 1/τ]}` of the support of `g`, but in general not on them. These
     points need not lie in `U`, even when `tsupport g` is a compact subset of `U`, because `U`
     is not assumed to be invariant under radial contractions. The hypothesis
     `tsupport g ⊆ B_β(0) ⊆ U` keeps all of them inside `U`. Steps 4 and 8 check it for every
     test function used.
   * **FTC in `s`.** `d/ds [sⁿ g(sx)] = n s^{n−1} g(sx) + sⁿ Dg(sx) x`. Integrating over
     `[1, 1/τ]` gives `τ^{-n} g(x/τ) − g(x) = n F(x) + DF(x) x`.
   * **Divergence.** `DX(x) v = F(x) v + (DF(x) v) x`. Wherever `p_x` is the projection onto an
     `n`-plane, which holds `μ`-a.e. by step 1,
     `div_M X = trace(DX(x) ∘ p_x) = n F(x) + DF(x)(p_x x) = τ^{-n} g(x/τ) − g(x) − DF(x)(x^⊥)`.
   * **First variation.** `∫ div_M X dμ = −∫ ⟨X, H⟩ dμ = −∫ F(x) ⟨x, H(x)⟩ dμ`.
     * Every integrand vanishes off `B_β(0)`.
     * On `B_β(0)`, each integrand is either bounded (by (i) and the bounds on `g` and `Dg`) or
       at most a constant times `|H|`.
     * `μ(B_β(0)) < ∞` and `H ∈ L¹(B_β(0), μ)`.

     So all integrals are finite. Substituting the formula for `div_M X` gives the conclusion.
3. **(P3) Layer-cake bound (Ch. 4, 4.11).**

   *Hypotheses.*
   * `ν` is a measure with `ν(B_R) < ∞`;
   * `w ≥ 0` is `ν`-integrable on `B_R`;
   * `m ∈ ℕ` and `0 < a ≤ R`;
   * `∫_{B_t} w dν ≤ K t^m` for every `t ∈ [a, R]`.

   *Conclusion.* `∫_{B_R ∖ B_a} |x|^{-m} w dν ≤ K (1 + m log(R/a))`.

   *Proof.* For `a < |x| ≤ R`,
   `|x|^{-m} = R^{-m} + ∫_a^R m t^{-m−1} 1{|x| < t} dt`.
   Integrate this against `w dν` over `B_R ∖ B_a`, and exchange the integrals by Fubini. The
   integrand is bounded by `m a^{-m−1} w`, so Fubini applies. The result is at most
   `R^{-m} · K R^m + ∫_a^R m t^{-m−1} · K t^m dt = K (1 + m log(R/a))`.
4. **(P2) Monotonicity identity (Ch. 4, 3.18; the book's (1)–(2), ll. 1184–1190).**

   For `σ ∈ [λ, 1]`, put `I_⊥(σ) = ∫_{B_1 ∖ B_σ} |x^⊥|² |x|^{-n−2} dμ`. Then
   `|(μ(B_1) − σ^{-n} μ(B_σ)) − I_⊥(σ)| ≤ δ (2 + log σ^{-1})`.

   *Proof.*
   * **Support ball.** `B_1` is compact and `U` is open. So some closed `ε`-thickening of
     `B_1` lies in `U` (`IsCompact.exists_cthickening_subset_open`). This thickening is
     `B_{1+ε}(0)` (`cthickening_closedBall`). Put `R′ = 1 + ε`.
   * **Cutoffs.** Put `η_k = ε/(k+1)`, `γ_k(u) = 1 − S((u − 1)/η_k)` and `g_k(y) = γ_k(|y|)`.
     * `g_k` is `C¹`: it is `≡ 1` near `0`, and it is a composition of `C¹` maps away from `0`.
     * `g_k` takes values in `[0, 1]`, equals `1` on `B_1`, and equals `0` for
       `|y| ≥ 1 + η_k`.

     So `tsupport g_k ⊆ B_{1+η_k}(0) ⊆ B_{R′}(0) ⊆ U`, and step 2 applies with `β = R′` and
     `τ = σ`.
   * **Radial reduction.** Put `q(x) = |x^⊥|²/|x|²`, which lies in `[0, 1]` by (i). Let
     `x ≠ 0`. By (ii), `Dg_k(sx)(x^⊥) = γ_k′(s|x|) ⟨x, x^⊥⟩/|x| = q(x) Dg_k(sx)(x)`.

     Put `L_k(x) = σ^{-n} g_k(x/σ) − g_k(x)`. The FTC identity of step 2 gives
     `J_k = q (L_k − n F_k)`. So step 2 reads
     `∫ L_k dμ = ∫ q (L_k − n F_k) dμ − ∫ F_k ⟨x, H⟩ dμ`.
   * **Limit `k → ∞`.** `g_k → 1_{B_1}` pointwise. Hence `L_k → L_∞ = σ^{-n} 1_{B_σ} − 1_{B_1}`
     and `F_k → F_∞`, where:
     * `F_∞ = (σ^{-n} − 1)/n` on `B_σ`;
     * `F_∞ = (|x|^{-n} − 1)/n` on `B_1 ∖ B_σ`;
     * `F_∞ = 0` off `B_1`.

     All integrands vanish off `B_{R′}(0)`. On `B_{R′}(0)` they are bounded by constants
     (`|L_k| ≤ σ^{-n} + 1` and `|F_k| ≤ σ^{1−n}(σ^{-1} − 1)`), or by a constant times `|H|`. So
     dominated convergence applies.
   * **Evaluation.** `∫ L_∞ dμ = σ^{-n} μ(B_σ) − μ(B_1)`, and
     `q (L_∞ − n F_∞) = −1_{B_1 ∖ B_σ} |x^⊥|² |x|^{-n−2}`. Therefore
     `(μ(B_1) − σ^{-n} μ(B_σ)) − I_⊥(σ) = ∫ F_∞ ⟨x, H⟩ dμ`.
   * **Error.** `|F_∞ ⟨x, H⟩| ≤ σ^{1−n}|H|/n` on `B_σ`, and `≤ |x|^{1−n}|H|/n` on
     `B_1 ∖ B_σ`. Use 0(a) at `t = σ`, and step 3 with `w = |H|`, `m = n − 1`, `K = δ`,
     `a = σ`, `R = 1` (its hypothesis is 0(a) for `t ∈ [σ, 1]`). The error is at most
     `δ/n + δ(1 + (n − 1) log σ^{-1})/n ≤ δ (2 + log σ^{-1})`.
5. **Mass bounds from (3.18).**
   * (a) For `σ ∈ [λ, 1]`: `σ^{-n} μ(B_σ) ≤ μ(B_1) + δ (2 + log σ^{-1}) ≤ Λ + 3δL`. This uses
     `I_⊥(σ) ≥ 0`, `log σ^{-1} ≤ L` and `L > 1`.
   * (b) `I_⊥(λ) ≤ |μ(B_1) − λ^{-n} μ(B_λ)| + δ (2 + L) ≤ ω_n δ + 2δ + δL ≤ (ω_n + 3) δ L`.
     This uses 0(b) and `L > 1`.
6. **Trivial case `dL > 1`.** The constant `C` of step 9 satisfies `C ≥ Λ + 3`. Put
   `A = B_{(1+d)ρ}(ξ) ∩ B_1`; step 11 uses the same set. In both cases (`dL > 1` here,
   `dL ≤ 1` in steps 7–11), the proof establishes two real inequalities between masses of
   subsets of `B_1`:
   * (R1) `μ(B_{(1−d)ρ}(ξ)) ≤ τ^{-n} μ(B_{τρ}(τξ)) + C d L`;
   * (R2) `τ^{-n} μ(B_{τρ}(τξ)) ≤ μ(A) + C d L`.

   Step 12 turns them into the two frozen inequalities. In the present case:
   * *(R1).* `μ(B_{(1−d)ρ}(ξ)) ≤ μ(B_1) ≤ Λ ≤ C ≤ C d L`, using 0(c), 0(e) and `dL > 1`.
     Adding the nonnegative term `τ^{-n} μ(B_{τρ}(τξ))` gives (R1).
   * *(R2).* Use 5(a) with `σ = τ`, then `δ ≤ d` and `dL ≥ 1`:
     `τ^{-n} μ(B_{τρ}(τξ)) ≤ τ^{-n} μ(B_τ) ≤ Λ + 3δL ≤ Λ + 3dL ≤ (Λ + 3) dL ≤ C d L`.
     Since `μ(A) ≥ 0`, this gives (R2).

   The remaining steps treat the case `dL ≤ 1`.
7. **The three annular integrals.** Since `dL ≤ 1`, also `δL ≤ dL ≤ 1`. So 5(a) gives
   `μ(B_t) ≤ (Λ + 3) tⁿ` for every `t ∈ [λ, 1]`. Define
   * `I_⊥ = ∫_{B_1 ∖ B_λ} |x^⊥|² |x|^{-n−2} dμ`,
   * `I_0 = ∫_{B_1 ∖ B_λ} |x|^{-n} dμ`,
   * `I_H = ∫_{B_1 ∖ B_λ} |x|^{1−n} |H| dμ`.

   Their bounds are:
   * `I_⊥ ≤ (ω_n + 3) δ L`, by 5(b);
   * `I_0 ≤ (Λ + 3)(1 + nL) ≤ (Λ + 3)(n + 1) L`, by step 3 with `w ≡ 1`, `m = n`,
     `K = Λ + 3`, `a = λ`, `R = 1`;
   * `I_H ≤ δ (1 + (n − 1) L) ≤ n δ L`, by step 3 with `w = |H|`, `m = n − 1`, `K = δ`,
     `a = λ`, `R = 1`, using 0(a).

   The bound for `I_H` is `nδL`, not `δL`. Step 3 gives only `δ(1 + (n − 1)L)`, which exceeds
   `δL` when `n ≥ 2`. This dimensional factor is the constant `C = C(n)` of the book's (3)
   (l. 1197), `∫_{B_1 ∖ B_λ} r^{1−n} |H| dμ ≤ C δ |log λ|`. Step 9 absorbs it into the final
   constant.
8. **(P4) Comparison for conical test functions.**

   *Hypotheses.*
   * `0 < λ ≤ τa`, `b ≤ 1`, `τ ∈ (0, 1]`, `ρ > 0` and `ε > 0`;
   * `χ, φ : ℝ → [0, 1]` are `C¹`;
   * `∫_α^β |χ′| ≤ 2` for all `α ≤ β`;
   * `|φ′| ≤ κ/ρ`, and `φ(t) = 0` for `t ≥ 2ρ`. This forces `κ ≥ 0`, since
     `0 ≤ |φ′(0)| ≤ κ/ρ` and `ρ > 0`; the Lean proof derives `κ ≥ 0` this way;
   * `g(y) = χ(|y|) φ(|y − ξ|)` is `C¹`, and `g(y) ≠ 0` implies `a < |y| < b`.

   *Conclusion.*
   `|τ^{-n} ∫ g(x/τ) dμ − ∫ g dμ| ≤ (2 + 2κε) I_⊥ + (2κ/ε) I_0 + 4ρ I_H`.

   *Proof.*
   * **Support hypothesis of step 2.** `{g ≠ 0} ⊆ {a < |y| < b}`. So
     `tsupport g ⊆ {a ≤ |y| ≤ b} ⊆ B_b(0) ⊆ B_1(0) ⊆ U`, using `b ≤ 1`. Hence step 2 applies
     with `β = b`, and the left side equals `|∫ J dμ − ∫ F ⟨x, H⟩ dμ|`.
   * **Localization to `B_1 ∖ B_λ`.** Let `x ∉ B_1 ∖ B_λ`. Then for every `s ∈ [1, 1/τ)`,
     `sx ∉ tsupport g`, so `g(sx) = 0` and `Dg(sx) = 0`:
     * if `|x| > 1`, then `|sx| > 1 ≥ b`;
     * if `|x| ≤ λ`, then `|sx| < λ/τ ≤ a`.

     Hence `J(x) = F(x) = 0`. Now let `x ∈ B_1 ∖ B_λ`, and let `s ≥ 1` with `sx ∈ tsupport g`.
     Then `s|x| ≤ b ≤ 1`, so `sⁿ ≤ |x|^{-n}` and `s^{n−1} ≤ |x|^{1−n}`.
   * **Ray segments.** If `|sx − ξ| < 2ρ`, then `|s − ⟨x, ξ⟩/|x|²| < 2ρ/|x|`. So these `s` lie
     in an interval of length `4ρ/|x|`.
   * **Derivative.** Let `sx ∉ {0, ξ}`; only one `s` has `sx = ξ`, a null set. By (ii),
     `Dg(sx)(x^⊥) = χ′(s|x|) φ(|sx − ξ|) |x^⊥|²/|x| + χ(s|x|) φ′(|sx − ξ|) ⟨(sx − ξ)/|sx − ξ|, x^⊥⟩`.
     A zero of the nonnegative `C¹` function `φ` is a minimum. So `φ′(t) ≠ 0` forces
     `φ(t) ≠ 0`, and hence `t < 2ρ`. Therefore
     `|Dg(sx)(x^⊥)| ≤ |χ′(s|x|)| |x^⊥|²/|x| + (κ/ρ) |x^⊥| 1{|sx − ξ| < 2ρ}`.
   * **Integration in `s`.** The change of variables `s ↦ s|x|` and the total-variation bound
     give `∫_1^{1/τ} |χ′(s|x|)| ds ≤ 2/|x|`. Put `u = |x^⊥|/|x|`. With the previous two bullets
     and `sⁿ ≤ |x|^{-n}`,
     `|J(x)| ≤ |x|^{-n} ((|x^⊥|²/|x|)(2/|x|) + (κ/ρ)|x^⊥|(4ρ/|x|)) = |x|^{-n} (2u² + 4κu)`.
   * **Young's inequality.** `2u² + 4κu ≤ (2 + 2κε) u² + 2κ/ε`, since the difference is
     `2κ(εu − 1)²/ε ≥ 0`. So
     `|J(x)| ≤ (2 + 2κε) |x^⊥|² |x|^{-n−2} + (2κ/ε) |x|^{-n}`.
   * **Curvature term.** `0 ≤ g ≤ 1`, and `g(sx) ≠ 0` forces `|sx − ξ| < 2ρ`. So
     `|F(x)| ≤ |x|^{1−n} · 4ρ/|x| = 4ρ |x|^{-n}`, and
     `|F(x) ⟨x, H(x)⟩| ≤ 4ρ |x|^{1−n} |H(x)|`.

   Integrating the bounds for `J` and `F ⟨x, H⟩` over `B_1 ∖ B_λ` proves the conclusion.
9. **Constants.** Put `κ = K_S/d` and `ε = d^{-2}`. Then `κεδ = K_S d` and `2κ/ε = 2 K_S d`.
   Use step 7, `δ ≤ d`, `ρ ≤ θ < 1` and `L > 1`. The error term of step 8 satisfies
   `E := (2 + 2κε) I_⊥ + (2κ/ε) I_0 + 4ρ I_H ≤ C′ d L`, where
   `C′ = 2(ω_n + 3)(1 + K_S) + 2 K_S (Λ + 3)(n + 1) + 4n`.
   The three terms of `C′` bound the three terms of `E`, in order.

   The constant of the theorem is `C = Λ + 3 + C′`. It depends only on `n` and `Λ`. The frozen
   statement allows `C = C(n, ℓ, Λ)`.
10. **First inequality.** For `c > dρ`, put `φ_c(t) = S((c − t)/(dρ))`. Apply step 8 with
    `a = 1/2`, `b = |ξ| + ρ`, `χ ≡ 1` (total variation `0`) and `φ = φ_ρ`. The hypotheses
    hold:
    * `λ ≤ τ/2` and `b ≤ 1`, by 0(e);
    * `|φ_ρ′| ≤ K_S/(dρ) = κ/ρ`;
    * `φ_ρ = 0` on `[ρ, ∞) ⊇ [2ρ, ∞)`, and `φ_ρ = 1` on `(−∞, (1−d)ρ]`;
    * `y ↦ φ_ρ(|y − ξ|)` is `C¹`, being `≡ 1` near `ξ`;
    * if `g(y) ≠ 0`, then `|y − ξ| < ρ`, so `1/2 < |ξ| − ρ < |y| < b`.

    Since `0 ≤ φ_ρ ≤ 1`, `φ_ρ = 1` on `(−∞, (1−d)ρ]` and `φ_ρ = 0` on `[ρ, ∞)`, we have
    `1_{B_{(1−d)ρ}(ξ)}(x) ≤ φ_ρ(|x − ξ|)` and `φ_ρ(|x/τ − ξ|) ≤ 1_{B_{τρ}(τξ)}(x)`. With step 8
    and `E ≤ C′ d L ≤ C d L` (step 9),
    `μ(B_{(1−d)ρ}(ξ)) ≤ ∫ φ_ρ(|x − ξ|) dμ ≤ τ^{-n} ∫ φ_ρ(|x/τ − ξ|) dμ + E ≤ τ^{-n} μ(B_{τρ}(τξ)) + C d L`.
    This is (R1). Both balls lie in `B_1`, by 0(e).
11. **Second inequality.** For `k ≥ 1`, apply step 8 with `a = 1/2`, `b = |ξ| + ρ`,
    `φ = φ_{(1+d)ρ}` and `χ_k(u) = S(k(u − 1/2)) · S(k(b − u))`. The hypotheses hold:
    * `χ_k = f₁ f₂`, where `f₁` is nondecreasing, `f₂` is nonincreasing, and both take values
      in `[0, 1]`. So `|χ_k′| ≤ f₁′ − f₂′`, and `∫_α^β |χ_k′| ≤ 2`.
    * `χ_k(u) = 0` unless `1/2 < u < b`, and `χ_k(u) → 1_{(1/2, b)}(u)` as `k → ∞`.
    * `φ_{(1+d)ρ} = 1` on `[0, ρ]`, and `φ_{(1+d)ρ} = 0` on `[(1+d)ρ, ∞) ⊇ [2ρ, ∞)`, because
      `d < 1`.
    * `g_k(y) = χ_k(|y|) φ_{(1+d)ρ}(|y − ξ|)` is `C¹`. It vanishes on the open ball
      `B̆_{1/2}(0)`, hence near `0`. Away from `0`, `χ_k(|y|)` is a composition of `C¹` maps,
      and `φ_{(1+d)ρ}(|y − ξ|)` is `C¹` because it is `≡ 1` near `ξ`.

    Step 8 gives `τ^{-n} ∫ g_k(x/τ) dμ ≤ ∫ g_k dμ + E`. If `g_k(y) ≠ 0`, then `|y| < b ≤ 1`
    and `|y − ξ| < (1+d)ρ`, so `y ∈ A = B_{(1+d)ρ}(ξ) ∩ B_1`, the set of step 6. As
    `0 ≤ g_k ≤ 1`, this gives `g_k ≤ 1_A`. With `E ≤ C′ d L ≤ C d L` (step 9), for every `k`,
    `τ^{-n} ∫ g_k(x/τ) dμ ≤ μ(A) + C d L`.

    Let `k → ∞`. For every `x`, `g_k(x/τ) → G(x) = 1{1/2 < |x/τ| < b} φ_{(1+d)ρ}(|x/τ − ξ|)`.
    The functions `x ↦ g_k(x/τ)` are dominated by `1_{B_1}`, which is `μ`-integrable by 0(c):
    they take values in `[0, 1]`, and `g_k(x/τ) ≠ 0` forces `|x| < τb ≤ 1`. By dominated
    convergence, `τ^{-n} ∫ G dμ ≤ μ(A) + C d L`.

    Next, `G = 1` on `B_{τρ}(τξ) ∖ {p}`, where `p = τ(1 + ρ/|ξ|)ξ`. Indeed, let `y = x/τ` with
    `|y − ξ| ≤ ρ`. Then:
    * `|y| ≥ |ξ| − ρ > 1/2`;
    * `|y| ≤ |ξ| + ρ = b`, with equality only if `y − ξ` is the nonnegative multiple of `ξ` of
      length `ρ`, i.e. `y = (1 + ρ/|ξ|)ξ`;
    * `φ_{(1+d)ρ}(|y − ξ|) = 1`.

    Also `μ({p}) = 0`, since `μ ≪ Hⁿ` and `Hⁿ{p} = 0` for `n ≥ 1`. As `G ≥ 0`, this gives
    `μ(B_{τρ}(τξ)) = μ(B_{τρ}(τξ) ∖ {p}) ≤ ∫ G dμ`. Therefore
    `τ^{-n} μ(B_{τρ}(τξ)) ≤ τ^{-n} ∫ G dμ ≤ μ(A) + C d L`.
    This is (R2). Here `B_{τρ}(τξ) ⊆ B_1` by 0(e), and `A ⊆ B_1`.
12. **Extended reals.** The real inequalities (R1) and (R2) involve only the masses of
    `B_{(1−d)ρ}(ξ)`, `B_{τρ}(τξ)` and `A`. All three sets lie in `B_1`, so their masses are
    finite by 0(c), and each mass equals `ofReal` of its real value (`ENNReal.ofReal_toReal`).
    The map `ofReal : ℝ → [0, ∞]` is monotone and preserves sums and products of nonnegative
    reals. Since `τ^{-n} ≥ 0` and `C d L ≥ 0`:
    * (R1) gives `μ(B_{(1−d)ρ}(ξ)) ≤ ofReal(τ^{-n}) μ(B_{τρ}(τξ)) + ofReal(C d L)`. This is the
      first frozen inequality (`hconv` in the Lean proof).
    * (R2) gives `ofReal(τ^{-n}) μ(B_{τρ}(τξ)) ≤ μ(A) + ofReal(C d L)`. Since
      `A ⊆ B_{(1+d)ρ}(ξ)`, monotonicity of `μ` in `[0, ∞]` gives `μ(A) ≤ μ(B_{(1+d)ρ}(ξ))`.
      Together these give the second frozen inequality (`hconv2`).

    The proof never uses `μ(B_{(1+d)ρ}(ξ))` as a real number and never claims that it is
    finite. The ball `B_{(1+d)ρ}(ξ)` need not lie in `B_1`: at the allowed endpoint `ρ = θ`,
    `|ξ| + (1+d)ρ = 1 + dθ > 1`. It need not lie in `U` either, and then 0(c) gives no bound
    for its mass. In Lean, `(V.weight S).toReal = 0` when `V.weight S = ∞`. So the real
    inequality with `μ(B_{(1+d)ρ}(ξ))` in place of `μ(A)` could fail if this mass were
    infinite, which is why the proof keeps `A`. The monotonicity step
    `μ(A) ≤ μ(B_{(1+d)ρ}(ξ))` holds in `[0, ∞]` in every case.

**Relation to the book.** The book's proof (ll. 1182–1300) combines (1)–(3) with first
variation for homogeneous degree-zero test functions, the co-area formula 2.9 of Ch. 3
(ll. 1229 and 1272) and Cauchy–Schwarz. The Lean proof uses the same estimates (1)–(3), as
steps 4, 5 and 7. In place of the homogeneous-function and co-area argument, it uses the direct
comparison of step 8: the radial field `F(x) x` of step 2, the test functions
`χ(|y|) φ(|y − ξ|)`, and Young's inequality. It does not use the co-area formula.

**Uses:** no sibling conjunct. The only accepted lemmas it uses are those of step 1.

### 4.10 Theorem 7.1, first assertion — `density_one_regularity` (issue #124, PR #5781, checkpoint `63173e03f8f2`)

1. Since `Θ = 1` and `H ∈ Lᵖ_loc`, there is a scale `r` at which the hypotheses 5.1 hold at
   `ξ` (`density_one_allard_scale`).
2. Theorem 5.2 applied to `V − ξ` (`exists_translated_varifold_allardHypotheses`) makes
   `(spt V − ξ) ∩ B_{γr}(0)` a rotated `C^{1,1−n/p}` graph.
3. On the open ball this graph is `graph_W u` for an open `W ∋ 0`
   (`exists_open_graph_domain_of_closedBall_graph`). The Hölder class follows from the finite
   scaled norm.
4. `Hⁿ(M ∆ spt V) = 0`, because `Θ ≥ 1` on `spt V`
   (`one_le_density_on_support_of_locallyLp`, `hausdorff_carrier_symmDiff_support_null`). This
   null set is transported by the isometry `x ↦ q⁻¹(x − ξ)`.

**Uses:** 5.2.

### 4.11 Theorem 7.1, second assertion — `density_one_higher_regularity` (issue #126, PR #5782, checkpoint `9c5cefba8e3e`)

1. Take `p = 2n/(1−α) > n`, so that `β = 1 − n/p = (1+α)/2`.
2. Theorem 5.2 at the density-one point gives a `C^{1,β}` graph.
3. Integrality of `θ` and monotonicity give `θ = 1`, `μ_V = Hⁿ ⌞ spt V` and `Θ = 1` on `spt V`
   near `ξ`. This uses the corrected monotonicity constant with an `ω_n`-normalized error.
4. Vertical test fields give the Euler–Lagrange (prescribed mean curvature) system for `u`.
5. Difference quotients and the Schauder interior estimate
   (`dohr_eb_schauder_interior_estimate`) bootstrap `u` to `C^{q+2,α}`.
6. Shrink to `ρ = min(r′, s)` and `W = {x ∈ B̆ⁿ_ρ(0) : |(x, u(x))| < ρ}`.

**Uses:** 5.2.

### 4.12 Corollary 7.3 — `regular_set_open_dense` (issue #128, PR #5582, checkpoint `7eeea44c01db`)

1. **`reg V` is relatively open.** `reg V = O ∩ spt V`, where `O` is the union of the regular
   balls (`rsod_regularSet_relOpen`). This uses the fact that `C¹` submanifolds restrict to open
   subsets.
2. **Every ball meets `reg V`.** Every open ball centred on `spt V` meets `reg V`
   (`rsod_regularSet_meets_ball`). Normalize `θ` by the least integer density `N` in the ball,
   then apply Theorem 5.2 at a point of density one.
3. **Closure.** `spt V = U ∩ spt μ_V` is closed in `U`, so `closure(reg V) ∩ U ⊆ spt V`.

**Uses:** 5.2.

### Dependency structure (extracted from the Lean source)

These are the direct references among the twelve conjunct theorems, read from the
comment-stripped source:

* 2.1, 2.5, 3.1 and 6.1 use none of the others;
* 2.6 ← 2.5;
* 2.7 ← 2.5;
* 4.5 ← 2.1, 2.5, 2.6, 3.1;
* 5.2 ← 2.5, 2.7, 4.5;
* 5.3 ← 5.2, 6.1, 4.5;
* 7.1(i) ← 5.2;
* 7.1(ii) ← 5.2;
* 7.3 ← 5.2.

This equals the `depends_on` lists of the accepted decomposition (`decomposition-v2.json`). The
graph is acyclic. No declaration refers to `main_theorem`, which is the last declaration of the
module, and Lean environments admit no forward references.

## 5. Historical decomposition versus lemmas actually used

* **Root history is unchanged.** The root's accepted outline
  (`nodes/root/natural-proof-source.md`: "follow the published proof" for each of the twelve
  conjuncts) and plan (`nodes/root/plan-source.md`: decompose along the conjuncts) are kept as
  history.
* **Decomposition history.** The first decomposition, `decomposition-v1.json`, was rejected with
  three required changes (`decomposition-review-receipt-v1.json`). The revision
  `decomposition-v2.json` was accepted (`decomposition-review-receipt-v2.json`). The final Lean
  route is exactly decomposition v2: twelve children, with the dependencies listed above.
* **Unused accepted lemmas.** Of the 541 accepted theorems, 533 are reachable from
  `main_theorem` in the source-level reference graph. The other 8 are accepted descendants of
  `density_one_higher_regularity` whose parents' final Lean proofs took other routes:
  * `dohr_translate_varifold` and its five children `dohr_tv_exists_translate`,
    `dohr_tv_weight_eq_map`, `dohr_tv_support_map_sub`, `dohr_tv_tangentProj_eq` and
    `dohr_tv_gmc_transfer`. The final proof of 7.1(ii) translates through
    `dohr_allard_graph_at_density_one` instead, which uses the accepted lemma
    `exists_translated_varifold_allardHypotheses`; 7.1(i) uses the same lemma.
  * `dohr_tp_weighted_tangent_of_lebesgue_point` and its child
    `dohr_tp_wtlp_ball_comparison_le`. Their parent `dohr_graph_tangent_planes` instead uses
    `dohr_tp_ae_weighted_tangent_of_growth`, `dohr_tp_graph_ball_growth`,
    `dohr_tp_graph_approx_tangent`, `dohr_tp_approx_tangent_affine_isometry` and
    `dohr_tp_projection_continuousOn`.

  They are kept unchanged, with their accepted names and types, to preserve the accepted child
  interfaces.
* **No root-level helper lemmas.** The root itself introduces no named helper lemma. The only
  root-level proof step is the anonymous constructor.

## 6. Library reuse provenance

All reused library results are existing, pinned declarations, used with their own proofs. None
of them is presented as new work.

* **Lean core:**
  * `And` (anonymous constructor, root step);
  * the tactic `as_aux_lemma` (child 6.1);
  * `Lean.Elab.Command.elabCommand`, `withEnableInfoTree` and the option `Elab.async`, used by
    the `elaborate_without_info_trees` command.
* **`simongmt`** (`Poincare.SimonGMT`, rev `2b3663083f3f`, from `lake-manifest.json`; `rg` finds
  no `sorry` and no `axiom` declaration in its sources):
  * Chapter 3:
    * `CountablyRectifiable` (used by the contract)
    * `HasApproximateTangentSpaceAt`
    * `HasWeightedApproximateTangentSpaceAt` and `HasWeightedApproximateTangentSpaceAt.unique`
    * `blowUpMap`
    * `regular_euclideanHausdorffMeasure_restrict_submodule`
  * Chapter 2:
    * `euclideanHausdorffMeasure_image_le_of_lipschitzOn`
    * `areaJacobianAt`, with `areaJacobianAt_nonneg`, `areaJacobianAt_eq_normDet` and
      `measurable_areaJacobianAt`
    * `areaRegularSet`, with `measurableSet_areaRegularSet` and
      `area_image_compl_regularSet_eq_zero`
    * `injective_area_formula_lipschitz`
    * `weighted_area_formula_lipschitz_injOn`
    * `integral_area_formula_of_injective_derivative`
    * `continuous_normDet`

  All of these are referenced by fully qualified name.
* **Mathlib** (rev `25730c7c`), for example:
  * Besicovitch differentiation: `Besicovitch.vitaliFamily`, `Besicovitch.ae_tendsto_rnDeriv`;
  * Vitali covering: `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`;
  * `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`;
  * Rademacher: `LipschitzWith.ae_differentiableAt`,
    `LipschitzOnWith.ae_differentiableWithinAt_of_mem`;
  * `lintegral_image_eq_lintegral_abs_deriv_mul`;
  * Lusin–Souslin: `MeasurableSet.image_of_continuousOn_injOn`;
  * `LipschitzOnWith.extend_real`;
  * `ContDiffBump`;
  * `InnerProductSpace.HarmonicOnNhd`;
  * `InnerProductSpace.volume_closedBall`;
  * `tendsto_integral_of_dominated_convergence`;
  * `intervalIntegral.integral_eq_sub_of_hasDerivAt`;
  * Fubini–Tonelli: `integral_prod`, `lintegral_prod`;
  * additionally named in §4.9 (Theorem 6.1):
    * the smooth step `Real.smoothTransition`, with its lemmas `contDiff`, `monotone`,
      `zero_of_nonpos`, `one_of_one_le`, `nonneg` and `le_one`;
    * `IsCompact.exists_cthickening_subset_open` and `cthickening_closedBall` (the ball
      `B_{1+ε}(0) ⊆ U`);
    * `hasFDerivAt_integral_of_dominated_of_fderiv_le` (differentiation under the integral sign
      in step 2);
    * `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` and
      `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`;
    * `MeasureTheory.integral_integral_swap` (Fubini in step 3);
    * `MeasureTheory.Measure.nullSingletonClass_hausdorff` (`Hⁿ{p} = 0` in step 11);
    * `MeasureTheory.measure_diff_null`, a deprecated alias of
      `MeasureTheory.measure_sdiff_null` (`μ(B_{τρ}(τξ) ∖ {p}) = μ(B_{τρ}(τξ))` in step 11);
    * for the conversions between real and extended-real masses (steps 0, 6 and 12):
      `ENNReal.ofReal_toReal`, `ENNReal.ofReal_mul`, `ENNReal.ofReal_add`,
      `ENNReal.ofReal_le_ofReal`, `ENNReal.toReal_nonneg`, `ENNReal.toReal_mono` and
      `ENNReal.toReal_le_of_le_ofReal`, and monotonicity of measures,
      `MeasureTheory.measure_mono`.
* **Proved in this run, not reused.** Several results are not in Mathlib or `simongmt`; they are
  proved by accepted nodes of this run:
  * the Poincaré inequality on balls (`w12_ball_poincare_inequality`);
  * Rellich compactness (`w12_ball_rellich_compactness`);
  * Weyl's lemma (`w12_ball_weyl_lemma`);
  * the Campanato estimates (`allard52_campanato_from_tilt`, `allard52_campanato_center_holder`,
    `allard52_campanato_ae_center`, `allard52_graph_campanato`, `any_radius_campanato`);
  * the Schauder interior estimate (`dohr_eb_schauder_interior_estimate`).

## 7. Reference use

`reference_use` (exactly one entry):

* **source:** `local-project`. Snapshot
  `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7`;
  `manifest.json` gives project `ea5607598f3133b40a13241f2e51517a8c6423cd` (the frozen commit)
  and mathlib `25730c7c759d108ef87ab70af2342a196760f79d` (the `lakefile.toml` pin).
* **Queries and findings** (paths relative to the snapshot):
  * `cmp project/GMT/Ch05/Submission.lean project/GMT/Ch05/Contract.lean`: identical. The
    snapshot's Submission is the 463-line byte copy of the contract, with
    `main_theorem := by sorry`.
  * `rg -n "theorem main_theorem" project`: 8 matches. These are the `Contract.lean` and
    `Submission.lean` stubs of Ch01, Ch02, Ch05 and Ch08. Ch05 has them at line 461 of both
    files. The snapshot contains no proof of the root.
  * `rg -c "TiltExcessHeightEstimate|…|RegularSetOpenDense"` (the twelve conjunct names):
    `project/GMT/Ch05/Contract.lean:14`, `project/GMT/Ch05/Submission.lean:14` and
    `project/GMT/Ch05/README.md:12`. Nowhere else.
  * `rg -l "tilt_excess_height_estimate|affine_approximation_lemma|…|regular_set_open_dense"`
    (the twelve child names): **no match**. Every child proof comes from this run's accepted
    checkpoints.
  * `rg -n "lipts_rectifiable_tangent_chart_cover|tdo_ods_integrableOn_norm_deriv|dohr_eb_elc2_averaged_hessian"`:
    **no match**. The three declarations touched by this repair exist only in this run's
    checkpoints.
  * `rg -n "elaborate_without_info_trees"`: **no match**. The command comes from the accepted
    checkpoint `14b7adf1a28b`.
  * `rg -l "withEnableInfoTree" mathlib/Mathlib`: `Tactic/DeriveCountable.lean` and
    `Tactic/DeriveEncodable.lean`. Mathlib's own command elaborators use the same core
    combinator.
  * Locations of the Mathlib items cited in §6:
    * `Analysis/Calculus/Rademacher.lean`: `LipschitzOnWith.ae_differentiableWithinAt_of_mem`
      (l. 361) and `LipschitzWith.ae_differentiableAt` (l. 385);
    * `MeasureTheory/Covering/Besicovitch.lean`: `Besicovitch.vitaliFamily` (l. 1021) and
      `ae_tendsto_rnDeriv` (l. 1078);
    * `MeasureTheory/Covering/Vitali.lean`:
      `exists_disjoint_subfamily_covering_enlargement_closedBall` (l. 158);
    * `MeasureTheory/Function/Jacobian.lean`:
      `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` (l. 255);
    * `MeasureTheory/Function/JacobianOneDim.lean`:
      `lintegral_image_eq_lintegral_abs_deriv_mul` (l. 44);
    * `MeasureTheory/Constructions/Polish/Basic.lean`:
      `MeasurableSet.image_of_continuousOn_injOn` (l. 821);
    * `Topology/MetricSpace/Lipschitz.lean`: `LipschitzOnWith.extend_real` (l. 308);
    * `Analysis/InnerProductSpace/Harmonic/Basic.lean`: `HarmonicAt` (l. 41) and
      `HarmonicOnNhd` (l. 48);
    * `MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`: `InnerProductSpace.volume_closedBall`
      (l. 354);
    * `MeasureTheory/Integral/DominatedConvergence.lean`:
      `tendsto_integral_of_dominated_convergence` (l. 57);
    * `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`:
      `integral_eq_sub_of_hasDerivAt` (l. 1148);
    * `Analysis/Calculus/BumpFunction/Basic.lean`: `ContDiffBump` (l. 70).
  * Locations of the Mathlib items added for §4.9:
    * `Analysis/SpecialFunctions/SmoothTransition.lean`: `def Real.smoothTransition` (l. 146),
      with `one_of_one_le` (l. 161), `zero_of_nonpos` (l. 168), `le_one` (l. 187), `nonneg`
      (l. 190), `contDiff` (l. 205) and `monotone` (l. 222);
    * `Topology/MetricSpace/Thickening.lean`: `IsCompact.exists_cthickening_subset_open`
      (l. 426);
    * `Analysis/Normed/Module/Ball/Pointwise.lean`: `cthickening_closedBall` (l. 318);
    * `Analysis/Calculus/ParametricIntegral.lean`:
      `hasFDerivAt_integral_of_dominated_of_fderiv_le` (l. 208);
    * `MeasureTheory/Integral/DominatedConvergence.lean`:
      `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` (l. 170) and
      `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` (l. 619);
    * `MeasureTheory/Integral/Prod.lean`: `integral_integral_swap` (l. 478);
    * `MeasureTheory/Measure/Hausdorff.lean`: `nullSingletonClass_hausdorff` (l. 615).
  * Locations of the Mathlib items added for the second revision of §4.9 (step 12 and its
    inputs). In this Mathlib revision, `Mathlib/Data/ENNReal/*.lean` are deprecated modules
    that only re-export `Mathlib/Basic/ENNReal/*.lean`. For example, `Data/ENNReal/Real.lean`
    consists of `public import Mathlib.Basic.ENNReal.Real` and `deprecated_module`. So
    `rg "(theorem|lemma) ofReal_toReal " mathlib/Mathlib/Data/ENNReal` finds **no match**, and
    the declarations are in:
    * `Basic/ENNReal/Basic.lean`: `ofReal_toReal` (l. 248) and `toReal_nonneg` (l. 276);
    * `Basic/ENNReal/Real.lean`: `ofReal_add` (l. 52), `toReal_mono` (l. 67),
      `ofReal_le_ofReal` (l. 137), `toReal_le_of_le_ofReal` (l. 283) and `ofReal_mul`
      (l. 297);
    * `MeasureTheory/OuterMeasure/Basic.lean`: `measure_mono` (l. 51), `measure_sdiff_null`
      (l. 99) and its deprecated alias `measure_diff_null` (l. 105).
  * `rg -n "conical_approximation_theorem|conical_P1|conical_P2|conical_P3|conical_P4" project`:
    **no match**. `rg -n "ConicalApproximationTheorem" project` finds only the frozen definition
    (`Contract.lean` and `Submission.lean`, l. 391), the `main_theorem` stubs (l. 461) and the
    README row for Theorem 6.1 (`project/GMT/Ch05/README.md:26`). The proof of §4.9 comes from
    the accepted checkpoint `0f113e83c542`.
* **Compatibility.** Every cited declaration comes from the pinned Mathlib and `simongmt`
  revisions used by the build. The comparator's axiom check covers them.

**Mathematical citation (not a `reference_use` entry).** Simon, *Introduction to Geometric
Measure Theory* (© Leon Simon 2014), <https://web.stanford.edu/class/math285/ts-gmt>. This is
the public copy that the prose audit cites for equation (3) of §6. I checked its title page and
table of contents (see the header of this document). Line numbers in this document refer to the
local source text.

## 8. Verification

All results below are for the final Lean file `GMT/Ch05/Submission.lean` (67617 lines, sha256
`ac23060c847cd402dc25b50bffa9413fa16281a4dd0689304cc280d5b76aaeb6`, first committed in
`26012c4a`).

### Exact configured comparator: passed

* **Run.** `env -u HF_TOKEN HUMANIZE_NODE_ID=root … python3 verifier/gmt-compare.py
  --lean-target GMT/Ch05/Submission.lean … --frozen-commit
  ea5607598f3133b40a13241f2e51517a8c6423cd root`, on candidate
  `26012c4ae4071cbf92436dec796a678f939b243e` (tree `22d3ec3778bc`).
* **Output.** "GMT comparator: comparator and Lean kernel accepted GMT.Ch05.main_theorem",
  "Your solution is okay!", exit 0.
* **Checks.** `exit_zero`, `lean_kernel_accepted` and `final_marker` are all true, with no
  post-check failures.
* **Configuration.** Challenge `GMT.Ch05.Contract`; solution `GMT.Ch05.Submission`; theorem
  `GMT.Ch05.main_theorem`; permitted axioms `propext`, `Quot.sound` and `Classical.choice`.
* **Evidence.** `cluster-state/verification/results/hoa63/20261013T143228Z-ch05-root-jq_k7qwl`,
  verdict key `bdb024590ba7fbf13282b2ca2a07bf69ad51a5c54d69eacf7a550703383470de`. The log
  contains no error, no redeclaration and no `dupNamespace` diagnostic.
* **Later commits.** Three later commits change only this document, so no comparator input
  changes:
  * `dc91aaf9` added it;
  * `20f58c4d` is its first revision (§3);
  * this commit is its second revision (§3).

  Their Lean and Lake inputs are byte-identical to `26012c4a`. The comparator's verdict key
  depends only on those inputs and the pinned verifier, so all of these commits have the same
  verdict key. The controller's runs of the same comparator on the first two confirm this. Each
  printed "identical inputs already passed every check" and "Your solution is okay!", and its
  `result.json` has status `passed`, the verdict key above, and `cached_from` pointing to the
  evidence directory above:
  * on `dc91aaf9`: `cluster-state/verification/results/hoa63/20261013T164526Z-ch05-root-tqevxcdb`
    (log `nodes/root/comparator-v1.log`);
  * on `20f58c4d`: `cluster-state/verification/results/hoa63/20261013T171557Z-ch05-root-y12amzmv`
    (log `nodes/root/comparator-v2.log`). `nodes/root/isolated-comparator-result.json` records
    `passed: true` for candidate `20f58c4d`.

  The receipts do not name the commit. The commit of each run is the branch head at that time.
  The first run started at 16:16:30 UTC and finished at 16:45:26, between `dc91aaf9`
  (16:12:28) and `20f58c4d` (17:14:52). The second started at 17:15:56, after `20f58c4d`.

### Child interfaces and axioms (scratch compile)

I made a scratch copy of the final file and compiled it with the pinned toolchain (`lean`
v4.35.0-rc3, with `LEAN_PATH` set to the pinned package builds). The copy adds the following
after `main_theorem`, inside `namespace GMT.Ch05`, which is the contract's scope at
`main_theorem`:

* 541 checks, one for each accepted DAG node below the root, each of the form
  `theorem _root_.ChildCheck.<lean_name> : (<lean_statement>) := by exact Submission.<lean_name>`.
  This is the comparator's own child-check form. Each `lean_statement` is the frozen one from
  `dag.json`, normalized by the verifier's `lean_contract.validate_lean_statement`.
* `#print axioms GMT.Ch05.main_theorem`.

Results:

* **Build.** Exit 0, no errors, no `sorry`.
* **Child checks.** 541/541 succeed: there is no diagnostic of any kind after line 67600. The
  only diagnostics in the whole file are 48 deprecation and style warnings inside child proofs.
* **Axioms.** `#print axioms` prints
  `'GMT.Ch05.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### Other checks

* **Contract constants.** All 80 `GMT.Ch05` constants of the contract preamble are identical
  under the contract's imports and the Submission's imports (§2).
* **Source checks.** Every accepted name is declared exactly once; there are no duplicates, no
  doubled namespace and no untracked helper added by the root; all 541 declarations are verbatim
  copies of their accepted checkpoints (§3).

## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Root delivery: merge the exact checked root PR, confirm the remote tree, then link and close child review PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
