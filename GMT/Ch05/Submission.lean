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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

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

namespace Submission

/-- Every `n`-dimensional subspace `T ⊆ ℝ^{n+ℓ}` is a rotated horizontal plane `q(ℝⁿ × {0})`.
Reindex an orthonormal basis of `T` (`stdOrthonormalBasis`) to `u : Fin n → ℝ^{n+ℓ}`, place it
at the indices `Fin.castAdd ℓ i` (`Fin.append u 0`) and extend it to an orthonormal basis `b` of
`ℝ^{n+ℓ}` (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`).  Then `q := b.repr.symm`
sends `e_{castAdd ℓ i}` to `b (castAdd ℓ i) = u i` (`OrthonormalBasis.repr_symm_single`), so
`q(span {e_{castAdd ℓ i}}) = span {u i} = T` (`Submodule.map_span`). -/
theorem tdo_exists_isometry_rotatedPlane : ∀ (n ℓ : ℕ) (T : Submodule ℝ (Amb n ℓ)),
    Module.finrank ℝ T = n → ∃ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, rotatedPlane q = T := by
  intro n ℓ T hT
  set bT : OrthonormalBasis (Fin n) ℝ T := (stdOrthonormalBasis ℝ T).reindex (finCongr hT)
  set u : Fin n → Amb n ℓ := fun i => (bT i : Amb n ℓ)
  have hu : Orthonormal ℝ u := bT.orthonormal.comp_linearIsometry T.subtypeₗᵢ
  set v : Fin (n + ℓ) → Amb n ℓ := Fin.append u fun _ => 0
  have hv : Orthonormal ℝ ((Set.range (Fin.castAdd ℓ)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    simp only [Set.domRestrict_apply, v, Fin.append_left]
    rw [orthonormal_iff_ite.mp hu i j]
    simp [Subtype.ext_iff]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨b.repr.symm, ?_⟩
  have hq : (fun i : Fin n => b.repr.symm (EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ))) =
      u := by
    funext i
    rw [OrthonormalBasis.repr_symm_single, hb _ ⟨i, rfl⟩]
    simp [v]
  rw [rotatedPlane, horizontalPlane, Submodule.map_span, ← Set.range_comp]
  change Submodule.span ℝ (Set.range fun i : Fin n =>
    b.repr.symm (EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ))) = T
  rw [hq, show u = T.subtype ∘ bT from rfl, Set.range_comp, Submodule.span_image,
    ← bT.coe_toBasis, bT.toBasis.span_eq, Submodule.map_subtype_top]
/-- Simon Ch. 5, proof of Theorem 4.5, step (1a): the weight `μ_V = (Hⁿ ⌞ M) ⌞ θ` of a
rectifiable varifold is concentrated on `spt V = U ∩ spt μ_V`. The support of a measure on the
second countable space `ℝ^{n+ℓ}` is conull (`Measure.support_mem_ae`), and `μ_V ≪ Hⁿ ⌞ M`
(`withDensity_absolutelyContinuous`), where `Hⁿ ⌞ M` is concentrated on the `Hⁿ`-null-measurable
carrier `M ⊆ U` (`ae_restrict_mem₀`). -/
theorem tdo_ghe_ae_mem_support : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), ∀ᵐ x ∂V.weight, x ∈ V.support := by
  intro n ℓ U V
  -- `μ_V`-a.e. point lies in `spt μ_V`
  have h1 : ∀ᵐ x ∂V.weight, x ∈ V.weight.support := Measure.support_mem_ae
  -- `μ_V`-a.e. point lies in `M`, since `Hⁿ ⌞ M`-a.e. point does and `μ_V ≪ Hⁿ ⌞ M`
  have h2 : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨V.carrier_subset hx2, hx1⟩
/-- Simon Ch. 5, proof of Theorem 4.5 (p. 120), the step "keeping in mind `θ(x) ≤ 1 + Cδ ≤ 2`"
comparing `μ_V` with `Hⁿ` on `B_{ησ}(τ) ∩ graph f`: if `θ ≤ C` holds `μ_V`-a.e. on a measurable set
`E`, then `∫_E g dμ_V ≤ C ∫_E g dHⁿ` for every measurable `g ≥ 0` (no sign condition on `C`, since
`ofReal C = 0` for `C < 0`). Write `μ_V = ν ⌞ ρ` with `ν = Hⁿ ⌞ M` and `ρ = ofReal ∘ θ`, which is
`ν`-a.e. measurable. Then `∫_E g dμ_V = ∫ ρ g d(ν ⌞ E)`; the hypothesis gives `θ(x) ≤ C` for
`ν`-a.e. `x ∈ E` with `ρ(x) ≠ 0`, so `ρ g ≤ ofReal(C) g` `(ν ⌞ E)`-a.e.; and
`ν ⌞ E = Hⁿ ⌞ (E ∩ M) ≤ Hⁿ ⌞ E`. -/
theorem tdo_ghe_setLIntegral_weight_le_mul : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (E : Set (Amb n ℓ)) (C : ℝ) (g : Amb n ℓ → ℝ≥0∞), MeasurableSet E → Measurable g → (∀ᵐ x ∂V.weight, x ∈ E → V.mult x ≤ C) → ∫⁻ x in E, g x ∂V.weight ≤ ENNReal.ofReal C * ∫⁻ x in E, g x ∂(μHE[n] : Measure (Amb n ℓ)) := by
  intro n ℓ U V E C g hE hg hC
  -- `μ_V = ν.withDensity ρ` with `ν = Hⁿ ⌞ M` and `ρ = ofReal ∘ θ`; `ρ` is a.e.-measurable for `ν`
  have hρ : AEMeasurable (fun x => ENNReal.ofReal (V.mult x))
      ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) :=
    V.aemeasurable_mult.ennreal_ofReal
  -- the bound `θ ≤ C` on `E` holds `ν`-a.e. where `ρ ≠ 0`
  have hCν : ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)).restrict V.carrier,
      ENNReal.ofReal (V.mult x) ≠ 0 → x ∈ E → V.mult x ≤ C :=
    (ae_withDensity_iff' hρ).mp hC
  -- hence `ρ g ≤ ofReal C · g` a.e. for `ν ⌞ E`
  have hle : ∀ᵐ x ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).restrict E,
      ENNReal.ofReal (V.mult x) * g x ≤ ENNReal.ofReal C * g x := by
    filter_upwards [ae_restrict_of_ae hCν, ae_restrict_mem hE] with x hx hxE
    rcases eq_or_ne (ENNReal.ofReal (V.mult x)) 0 with h0 | h0
    · rw [h0, zero_mul]
      exact zero_le
    · gcongr
      exact hx h0 hxE
  -- `ν ⌞ E = Hⁿ ⌞ (E ∩ M) ≤ Hⁿ ⌞ E`
  have hνE : ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).restrict E ≤
      (μHE[n] : Measure (Amb n ℓ)).restrict E := by
    rw [Measure.restrict_restrict hE]
    exact Measure.restrict_mono inter_subset_left le_rfl
  calc ∫⁻ x in E, g x ∂V.weight
      = ∫⁻ x, ENNReal.ofReal (V.mult x) * g x
          ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).restrict E := by
        rw [RectifiableVarifold.weight, restrict_withDensity hE,
          lintegral_withDensity_eq_lintegral_mul₀ hρ.restrict hg.aemeasurable]
        rfl
    _ ≤ ∫⁻ x, ENNReal.ofReal C * g x
          ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).restrict E := lintegral_mono_ae hle
    _ = ENNReal.ofReal C * ∫⁻ x, g x
          ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).restrict E := lintegral_const_mul _ hg
    _ ≤ ENNReal.ofReal C * ∫⁻ x in E, g x ∂(μHE[n] : Measure (Amb n ℓ)) := by
        gcongr ENNReal.ofReal C * ?_
        exact lintegral_mono' hνE le_rfl
/-- Simon Ch. 5, proof of Theorem 4.5, between (19) and (20): for `r > 0` and `φ` continuous and
nonnegative on the closed ball `B_r(0) ⊆ ℝⁿ`,
`∫⁻_{B_r(0)} ofReal(φ) dLⁿ = ofReal(∫_{B̆_r(0)} φ dLⁿ)`, with a Bochner integral over the open
ball on the right.  The sphere `∂B_r(0)` is `Lⁿ`-null since `r ≠ 0`, so the two balls agree up to
a null set; `φ` is integrable on the compact `B_r(0)`, hence on `B̆_r(0)`, and nonnegative there. -/
theorem tdo_ghe_lintegral_closedBall_ofReal_eq : ∀ (n : ℕ) (φ : Rn n → ℝ) (r : ℝ), 0 < r → ContinuousOn φ (closedBall 0 r) → (∀ x ∈ closedBall (0 : Rn n) r, 0 ≤ φ x) → ∫⁻ x in closedBall (0 : Rn n) r, ENNReal.ofReal (φ x) = ENNReal.ofReal (∫ x in ball (0 : Rn n) r, φ x) := by
  intro n φ r hr hφ hφ0
  -- Steps 1–2: `Lⁿ(∂B_r(0)) = 0`, so `Lⁿ(B_r(0)) ≤ Lⁿ(B̆_r(0)) + Lⁿ(∂B_r(0)) = Lⁿ(B̆_r(0))` and
  -- the open and closed balls agree a.e.
  have hae : ball (0 : Rn n) r =ᵐ[volume] closedBall (0 : Rn n) r := by
    refine ae_eq_of_subset_of_measure_ge ball_subset_closedBall ?_
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
    calc volume (closedBall (0 : Rn n) r)
        = volume (ball (0 : Rn n) r ∪ sphere 0 r) := by rw [ball_union_sphere]
      _ ≤ volume (ball (0 : Rn n) r) + volume (sphere (0 : Rn n) r) := measure_union_le _ _
      _ = volume (ball (0 : Rn n) r) := by
        rw [Measure.addHaar_sphere_of_ne_zero volume 0 hr.ne', add_zero]
  rw [← setLIntegral_congr hae]
  -- Step 3: `φ` is integrable on the compact closed ball, hence on the open ball.
  have hint : IntegrableOn φ (ball (0 : Rn n) r) :=
    (hφ.integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  -- Step 4: `φ ≥ 0` on the open ball.
  have hnn : 0 ≤ᵐ[volume.restrict (ball (0 : Rn n) r)] φ :=
    ae_restrict_of_forall_mem measurableSet_ball fun x hx => hφ0 x (ball_subset_closedBall hx)
  -- Steps 5–6: convert the Bochner integral of the integrable nonnegative `φ`.
  exact (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
/-- Simon Ch. 5, Lemma 2.6 and its proof (pp. 110–111): graph coordinates on
`ℝ^{n+ℓ} = ℝⁿ × ℝ^ℓ` and the projection onto `T₀ = q(ℝⁿ × {0})`, the plane the book takes to be
`ℝⁿ × {0}` without loss of generality. For a linear isometry `q` of `ℝ^{n+ℓ}`:
(i) `(a, b) − (a', b') = (a − a', b − b')`; (ii) `|(a, b)|² = |a|² + |b|²`; (iii) every
`z ∈ ℝ^{n+ℓ}` is some `(a, b)`; (iv) `p_{T₀}(q(a, b)) = q(a, 0)`.
The coordinate of `(a, b)` at `castAdd ℓ i` is `a_i` and at `natAdd n j` is `b_j`, and every index
of `Fin (n + ℓ)` has one of these forms (`Fin.addCases`); this gives (i) and (iii), and (ii) by
splitting `Σ_k z_k²` with `Fin.sum_univ_add`. For (iv), `(a, 0) = Σ_i a_i e_{castAdd ℓ i}` lies in
`ℝⁿ × {0}`, `(0, b)` is orthogonal to every `e_{castAdd ℓ i}` and hence to `ℝⁿ × {0}`, and `q`
preserves inner products; so `q(a, 0) ∈ T₀` and `q(a, b) − q(a, 0) = q(0, b) ⊥ T₀`, which
characterizes `q(a, 0)` as the orthogonal projection of `q(a, b)` onto `T₀`. -/
theorem lip_approx_graph_coordinates : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b')) ∧ (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧ (∀ z : Amb n ℓ, ∃ (a : Rn n) (b : Rn ℓ), z = graphPoint a b) ∧ (∀ (a : Rn n) (b : Rn ℓ), (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a 0)) := by
  intro n ℓ q
  -- the coordinates of `graphPoint a b`
  have hl : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp [graphPoint]
  have hr : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp [graphPoint]
  -- (i): subtraction is coordinatewise
  have hsub : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b') := by
    intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.sub_apply, hl]
    · simp only [PiLp.sub_apply, hr]
  refine ⟨hsub, ?_, ?_, ?_⟩
  -- (ii): split `‖z‖² = Σ_k ‖z_k‖²` over the two blocks of indices
  · intro a b
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp only [hl, hr]
  -- (iii): read off `a` and `b` from the two blocks of coordinates of `z`
  · intro z
    refine ⟨WithLp.toLp 2 (fun i => z (Fin.castAdd ℓ i)),
      WithLp.toLp 2 (fun j => z (Fin.natAdd n j)), ?_⟩
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [hl]
    · rw [hr]
  -- (iv)
  · intro a b
    -- `graphPoint a 0 = Σ_i a_i e_{castAdd ℓ i}` lies in `ℝⁿ × {0}`
    have hmem : graphPoint a 0 ∈ horizontalPlane n ℓ := by
      have e : graphPoint a 0 =
          ∑ i : Fin n, a i • EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) := by
        ext k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · rw [hl]
          simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, Finset.sum_apply,
            Pi.smul_apply, Pi.single_apply, Fin.castAdd_inj, smul_eq_mul, mul_ite, mul_one,
            mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        · rw [hr]
          simp only [PiLp.zero_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single,
            Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          refine (Finset.sum_eq_zero fun x _ => ?_).symm
          have hne : Fin.natAdd n j ≠ Fin.castAdd ℓ x := by
            intro h
            have h' := congrArg Fin.val h
            simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
            have := x.isLt
            omega
          rw [Pi.single_eq_of_ne hne, mul_zero]
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    -- `graphPoint 0 b` is orthogonal to every `e_{castAdd ℓ i}`, hence to `ℝⁿ × {0}`
    have horth : ∀ h ∈ horizontalPlane n ℓ, inner ℝ (graphPoint 0 b) h = 0 := by
      have hle : horizontalPlane n ℓ ≤ (ℝ ∙ graphPoint 0 b)ᗮ := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
          EuclideanSpace.inner_single_right, hl]
        simp
      intro h hh
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hh)
    -- `q(a, 0) ∈ T₀`, and `q(a, b) - q(a, 0) = q(0, b)` is orthogonal to `T₀ = q(ℝⁿ × {0})`
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.mem_map_of_mem hmem) ?_
    intro w hw
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hw
    rw [← map_sub, hsub, sub_self, sub_zero]
    exact (q.inner_map_map _ _).trans (horth h hh)
/-- Simon Ch. 5, proof of Theorem 4.5 (pp. 116–120), integrals over the Lipschitz graph: for a
linear isometry `q` of `ℝ^{n+ℓ}` and `f : ℝⁿ → ℝ^ℓ` that is `L`-Lipschitz on `D`, the map
`F(x) = q(x, f(x))` is `√(1 + L²)`-Lipschitz on `D`.  Since `q` preserves distances and
`|(x, f x) − (y, f y)|² = |x − y|² + |f(x) − f(y)|²` (split the sum `Σ_k w_k²` over the indices
`castAdd ℓ i` and `natAdd n j` of `Fin (n + ℓ)` with `Fin.sum_univ_add`), the hypothesis gives
`|F(x) − F(y)|² ≤ (1 + L²)|x − y|² = (√(1 + L²) |x − y|)²` for `x, y ∈ D`; take square roots. -/
theorem tdo_gl_graph_map_lipschitzOn : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (D : Set (Rn n)) (L : ℝ≥0), LipschitzOnWith L f D → LipschitzOnWith (NNReal.sqrt (1 + L ^ 2)) (fun x => q (graphPoint x (f x))) D := by
  intro n ℓ q f D L hf
  -- the coordinates of `graphPoint a b`
  have hl : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp [graphPoint]
  have hr : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp [graphPoint]
  -- `|(a, b) − (a', b')|² = |a − a'|² + |b − b'|²`, splitting `Σ_k w_k²` over the two blocks
  have hsq : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      ‖graphPoint a b - graphPoint a' b'‖ ^ 2 = ‖a - a'‖ ^ 2 + ‖b - b'‖ ^ 2 := by
    intro a a' b b'
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp only [PiLp.sub_apply, hl, hr]
  -- `q` preserves distances, so it suffices to bound `|(x, f x) − (y, f y)|` by
  -- `√(1 + L²) |x − y|` for `x, y ∈ D`
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [LinearIsometryEquiv.dist_map, dist_eq_norm, dist_eq_norm, Real.coe_sqrt, NNReal.coe_add,
    NNReal.coe_one, NNReal.coe_pow]
  -- `|f x − f y|² ≤ L² |x − y|²` on `D`
  have hfxy : ‖f x - f y‖ ^ 2 ≤ (L * ‖x - y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hf.norm_sub_le hx hy) 2
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [hsq, mul_pow, Real.sq_sqrt (by positivity)]
  rw [mul_pow] at hfxy
  linarith
/-- The graph point `(x, y) ∈ ℝ^{n+ℓ}` is the inverse image of `(x, y)` under Mathlib's canonical
equivalence `EuclideanSpace.finAddEquivProd : ℝ^{n+ℓ} ≃L[ℝ] ℝⁿ × ℝ^ℓ` (reindexing by
`finSumFinEquiv.symm`, then splitting into the `Sum.inl`/`Sum.inr` parts).  Compare coordinates:
every index of `Fin (n + ℓ)` is `Fin.castAdd ℓ j` or `Fin.natAdd n k` (`Fin.addCases`); there both
sides equal `x j`, resp. `y k` (`Fin.append_left`/`Fin.append_right` on the left,
`finSumFinEquiv_symm_apply_castAdd`/`finSumFinEquiv_symm_apply_natAdd` on the right). -/
theorem rsod_graphPoint_eq_finAddEquivProd_symm : ∀ {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ),
    graphPoint x y = (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm (x, y) := by
  intro n ℓ x y
  ext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp [graphPoint]
  · simp [graphPoint]
/-- **Hilbert–Schmidt versus operator norm** (Simon, Notation p. ix), as used in the hole estimate
of the proof of Ch. 5, Corollary 2.7 (`‖A‖ ≤ |A|`).  For `A : ℝᵐ →L ℝᵏ` the squared Hilbert–Schmidt
norm `|A|² = Σᵢ |A eᵢ|²` is continuous in `A` (a finite sum of squared norms of the evaluations
`A ↦ A eᵢ`) and satisfies `0 ≤ |A|² ≤ m ‖A‖²` (`|A eᵢ| ≤ ‖A‖ |eᵢ| = ‖A‖`).  Moreover
`|A v|² ≤ |A|² |v|²`: expanding `v = Σᵢ vᵢ eᵢ` gives `|A v| ≤ Σᵢ |vᵢ| |A eᵢ|`, and Cauchy–Schwarz
bounds the square of the right side by `(Σᵢ |vᵢ|²)(Σᵢ |A eᵢ|²) = |v|² |A|²`. -/
theorem lgc_hsNormSq_bounds : ∀ (m k : ℕ), Continuous (fun A : Rn m →L[ℝ] Rn k => hsNormSq A) ∧ ∀ A : Rn m →L[ℝ] Rn k, 0 ≤ hsNormSq A ∧ hsNormSq A ≤ m * ‖A‖ ^ 2 ∧ ∀ v : Rn m, ‖A v‖ ^ 2 ≤ hsNormSq A * ‖v‖ ^ 2 := by
  intro m k
  refine ⟨?_, fun A => ⟨?_, ?_, fun v => ?_⟩⟩
  · -- Continuity: a finite sum of `‖A eᵢ‖ ^ 2`, each continuous in `A`.
    unfold hsNormSq
    fun_prop
  · unfold hsNormSq
    positivity
  · -- `‖A eᵢ‖ ≤ ‖A‖ ‖eᵢ‖ = ‖A‖` for each of the `m` summands.
    unfold hsNormSq
    calc ∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2 ≤ ∑ _i : Fin m, ‖A‖ ^ 2 := by
          gcongr with i
          calc ‖A (EuclideanSpace.single i 1)‖ ≤ ‖A‖ * ‖EuclideanSpace.single i (1:ℝ)‖ :=
                A.le_opNorm _
            _ = ‖A‖ := by simp
      _ = m * ‖A‖ ^ 2 := by simp
  · unfold hsNormSq
    set e : Fin m → Rn m := fun i => EuclideanSpace.single i 1 with he
    -- Expand `v` in the standard basis and apply the triangle inequality.
    have hv : v = ∑ i, v i • e i := by
      ext j
      simp [he, Pi.single_apply]
    have hAv : A v = ∑ i, v i • A (e i) := by
      conv_lhs => rw [hv]
      simp [map_sum, map_smul]
    have h1 : ‖A v‖ ≤ ∑ i, |v i| * ‖A (e i)‖ := by
      rw [hAv]
      calc _ ≤ ∑ i, ‖v i • A (e i)‖ := norm_sum_le _ _
        _ = _ := by simp [norm_smul]
    -- Cauchy–Schwarz for the finite sums, and `‖v‖² = Σᵢ |vᵢ|²`.
    have h2 : (∑ i, |v i| * ‖A (e i)‖) ^ 2 ≤ (∑ i, |v i| ^ 2) * (∑ i, ‖A (e i)‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : ‖v‖ ^ 2 = ∑ i, |v i| ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [sq_abs]
    have h0 : 0 ≤ ‖A v‖ := norm_nonneg _
    calc ‖A v‖ ^ 2 ≤ (∑ i, |v i| * ‖A (e i)‖) ^ 2 := by gcongr
      _ ≤ (∑ i, |v i| ^ 2) * (∑ i, ‖A (e i)‖ ^ 2) := h2
      _ = (∑ i, ‖A (e i)‖ ^ 2) * ‖v‖ ^ 2 := by rw [h3, mul_comm]

/-- The rotated graph plane `q{(v, Av) : v ∈ ℝⁿ}` of a linear map `A : ℝⁿ → ℝ^ℓ` is
`n`-dimensional.  With `E = EuclideanSpace.finAddEquivProd`, `graphPoint v (A v) = E.symm (v, A v)`
(`rsod_graphPoint_eq_finAddEquivProd_symm`), so the generators are the values of the linear map
`Φ = q ∘ E.symm ∘ (id, A)` and their span is `range Φ` (`Submodule.span_eq`).  `Φ` is injective,
since `q` and `E.symm` are and `(v, A v)` determines `v`; hence
`finrank (range Φ) = finrank ℝⁿ = n` (`LinearMap.finrank_range_of_inj`). -/
theorem tdo_gpd_graph_plane_finrank : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ),
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v)))) = n := by
  intro n ℓ q A
  let E : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ := EuclideanSpace.finAddEquivProd
  let Φ : Rn n →ₗ[ℝ] Amb n ℓ := q.toLinearEquiv.toLinearMap ∘ₗ
    E.symm.toLinearEquiv.toLinearMap ∘ₗ LinearMap.id.prod A.toLinearMap
  have hΦ : ∀ v, Φ v = q (graphPoint v (A v)) := fun v => by
    rw [rsod_graphPoint_eq_finAddEquivProd_symm]
    rfl
  have hinj : Function.Injective Φ := fun v w hvw => by
    rw [hΦ, hΦ, rsod_graphPoint_eq_finAddEquivProd_symm,
      rsod_graphPoint_eq_finAddEquivProd_symm] at hvw
    exact (Prod.mk.inj (E.symm.injective (q.injective hvw))).1
  have hrange : (Set.range fun v : Rn n => q (graphPoint v (A v))) =
      (LinearMap.range Φ : Set (Amb n ℓ)) := by
    rw [LinearMap.coe_range]
    exact congrArg Set.range (funext fun v => (hΦ v).symm)
  rw [hrange, Submodule.span_eq, LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]

/-- Simon Ch. 5, Lemma 2.6 and its proof (pp. 110–111): the distance from `q(a, b)` to the plane
`T₀ = q(ℝⁿ × {0})` is `|b|`. By `lip_approx_graph_coordinates`, the points of `T₀` are exactly the
`q(c, 0)` (each `q(c, 0) = p_{T₀}(q(c, 0))` lies in `T₀`, and `p ∈ T₀` with `q⁻¹(p) = (c, d)` gives
`p = p_{T₀}(p) = q(c, 0)`), and `|q(a, b) − q(c, 0)| = |(a − c, b)| ≥ |b|`, with equality at
`c = a`. -/
theorem tdo_gpd_infDist_rotatedPlane_graphPoint : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (a : Rn n) (b : Rn ℓ), infDist (q (graphPoint a b)) (rotatedPlane q : Set (Amb n ℓ)) = ‖b‖ := by
  intro n ℓ q a b
  obtain ⟨hsub, hnorm, hsurj, hproj⟩ := lip_approx_graph_coordinates n ℓ q
  -- `|b| ≤ |(c, b)|` and `|(0, b)| = |b|`
  have hge : ∀ (c : Rn n) (d : Rn ℓ), ‖d‖ ≤ ‖graphPoint c d‖ := by
    intro c d
    have h := hnorm c d
    have h0 : 0 ≤ ‖graphPoint c d‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖c‖, norm_nonneg d]
  have hzero : ∀ d : Rn ℓ, ‖graphPoint (0 : Rn n) d‖ = ‖d‖ := by
    intro d
    have h := hnorm 0 d
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  -- every `q(c, 0)` lies in `T₀`
  have hmem : ∀ c : Rn n, q (graphPoint c 0) ∈ rotatedPlane q := by
    intro c
    rw [← hproj c 0]
    exact Submodule.starProjection_apply_mem _ _
  -- every point of `T₀` is some `q(c, 0)`
  have hform : ∀ p ∈ rotatedPlane q, ∃ c : Rn n, p = q (graphPoint c 0) := by
    intro p hp
    obtain ⟨c, d, hcd⟩ := hsurj (q.symm p)
    have hp' : p = q (graphPoint c d) := by
      rw [← hcd]
      simp
    refine ⟨c, ?_⟩
    have h := hproj c d
    rw [← hp', Submodule.starProjection_eq_self_iff.mpr hp] at h
    exact h
  apply le_antisymm
  -- upper bound: compare with `q(a, 0) ∈ T₀`
  · calc infDist (q (graphPoint a b)) (rotatedPlane q : Set (Amb n ℓ))
        ≤ dist (q (graphPoint a b)) (q (graphPoint a 0)) := infDist_le_dist_of_mem (hmem a)
      _ = ‖b‖ := by
        rw [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, hsub, sub_self, sub_zero,
          hzero]
  -- lower bound: `|q(a, b) − q(c, 0)| = |(a − c, b)| ≥ |b|` for every `q(c, 0) ∈ T₀`
  · rw [le_infDist ⟨0, (rotatedPlane q).zero_mem⟩]
    intro p hp
    obtain ⟨c, rfl⟩ := hform p hp
    rw [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, hsub, sub_zero]
    exact hge _ _
/-- Simon Ch. 5, proof of Theorem 4.5 (p. 120): the `n`-dimensional subspace `S`, the graph of the
linear part of the affine `λ`, in rotated coordinates.  For a linear isometry `q` of `ℝ^{n+ℓ}` and a
linear `A : ℝⁿ → ℝ^ℓ` let `S = span{q(v, A v) : v ∈ ℝⁿ}` and `T₀ = q(ℝⁿ × {0})`.  Then
(i) `dim S = n`; (ii) `dist(x, S) ≤ dist(x, T₀) + |A| |x|`;
(iii) `dist(q(x', y) − q(0, c), S) ≤ |y − (c + A x')|`
(the book's `dist(x, ξ + S) ≤ |f(x') − λ(x')|` for `x = (x', f(x'))`, `ξ = (0, λ(0))`);
(iv) `|x'| ≤ |q(x', y) − q(0, c)|`; (v) `|q(0, c)| = |c|`.
(i) is `tdo_gpd_graph_plane_finrank`.  The points `Φ(v) = q(v, A v)` lie in `S`, `q` is a linear
isometry, and `(a, b) − (a', b') = (a − a', b − b')`, `|(a, b)|² = |a|² + |b|²`
(`lip_approx_graph_coordinates`).  Hence `q(x', y) − q(0, c) = q(x', y − c)`, which gives (iv) and
(v), and its difference with `Φ(x')` is `q(0, y − (c + A x'))`, which gives (iii).  For (ii) write
`x = q(a, b)`: then `dist(x, T₀) = |b|` (`tdo_gpd_infDist_rotatedPlane_graphPoint`) and
`dist(x, S) ≤ |x − Φ(a)| = |b − A a| ≤ |b| + |A| |a| ≤ |b| + |A| |x|`, by `|A a| ≤ |A| |a|`
(Cauchy–Schwarz, `lgc_hsNormSq_bounds`) and `|a| ≤ |(a, b)| = |x|`. -/
theorem tdo_graph_plane_dist : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ), Module.finrank ℝ (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v)))) = n ∧ (∀ x : Amb n ℓ, infDist x (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) : Set (Amb n ℓ)) ≤ infDist x (rotatedPlane q : Set (Amb n ℓ)) + hsNorm A * ‖x‖) ∧ (∀ (x' : Rn n) (y c : Rn ℓ), infDist (q (graphPoint x' y) - q (graphPoint (0 : Rn n) c)) (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) : Set (Amb n ℓ)) ≤ ‖y - (c + A x')‖) ∧ (∀ (x' : Rn n) (y c : Rn ℓ), ‖x'‖ ≤ ‖q (graphPoint x' y) - q (graphPoint (0 : Rn n) c)‖) ∧ ∀ c : Rn ℓ, ‖q (graphPoint (0 : Rn n) c)‖ = ‖c‖ := by
  intro n ℓ q A
  obtain ⟨hsub, hnorm, hsurj, -⟩ := lip_approx_graph_coordinates n ℓ q
  set S := Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v)))
  -- `‖a‖ ≤ ‖(a, b)‖` and `‖(0, b)‖ = ‖b‖`
  have hle : ∀ (a : Rn n) (b : Rn ℓ), ‖a‖ ≤ ‖graphPoint a b‖ := by
    intro a b
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [hnorm]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hzero : ∀ b : Rn ℓ, ‖graphPoint (0 : Rn n) b‖ = ‖b‖ := by
    intro b
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [hnorm, norm_zero, zero_pow two_ne_zero, zero_add]
  -- `‖A a‖ ≤ |A| ‖a‖`, the square root of `‖A a‖² ≤ |A|² ‖a‖²`
  have hA : ∀ a : Rn n, ‖A a‖ ≤ hsNorm A * ‖a‖ := by
    intro a
    obtain ⟨h0, -, hAa⟩ := (lgc_hsNormSq_bounds n ℓ).2 A
    calc ‖A a‖ = Real.sqrt (‖A a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (hsNormSq A * ‖a‖ ^ 2) := Real.sqrt_le_sqrt (hAa a)
      _ = hsNorm A * ‖a‖ := by rw [Real.sqrt_mul h0, Real.sqrt_sq (norm_nonneg _), hsNorm]
  -- the points `Φ(v) = q(v, A v)` of `S`, and `q(x', y) - q(0, c) = q(x', y - c)`
  have hmem : ∀ v : Rn n, q (graphPoint v (A v)) ∈ S := fun v => Submodule.subset_span ⟨v, rfl⟩
  have hdiff : ∀ (x' : Rn n) (y c : Rn ℓ),
      q (graphPoint x' y) - q (graphPoint (0 : Rn n) c) = q (graphPoint x' (y - c)) := by
    intro x' y c
    rw [← map_sub, hsub, sub_zero]
  refine ⟨Submission.tdo_gpd_graph_plane_finrank n ℓ q A, fun x => ?_, fun x' y c => ?_,
    fun x' y c => ?_, fun c => ?_⟩
  -- (ii): write `x = q(a, b)`; then `dist(x, T₀) = ‖b‖` and `dist(x, S) ≤ ‖x - Φ(a)‖`
  · obtain ⟨a, b, hab⟩ := hsurj (q.symm x)
    obtain rfl : x = q (graphPoint a b) := by rw [← hab, LinearIsometryEquiv.apply_symm_apply]
    rw [Submission.tdo_gpd_infDist_rotatedPlane_graphPoint n ℓ q a b,
      LinearIsometryEquiv.norm_map]
    calc infDist (q (graphPoint a b)) (S : Set (Amb n ℓ))
        ≤ dist (q (graphPoint a b)) (q (graphPoint a (A a))) := infDist_le_dist_of_mem (hmem a)
      _ = ‖b - A a‖ := by
        rw [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, hsub, sub_self, hzero]
      _ ≤ ‖b‖ + ‖A a‖ := norm_sub_le _ _
      _ ≤ ‖b‖ + hsNorm A * ‖graphPoint a b‖ := by
        gcongr
        exact (hA a).trans (mul_le_mul_of_nonneg_left (hle a b) (Real.sqrt_nonneg _))
  -- (iii): compare with `Φ(x') ∈ S`
  · calc infDist (q (graphPoint x' y) - q (graphPoint (0 : Rn n) c)) (S : Set (Amb n ℓ))
        ≤ dist (q (graphPoint x' y) - q (graphPoint (0 : Rn n) c)) (q (graphPoint x' (A x'))) :=
          infDist_le_dist_of_mem (hmem x')
      _ = ‖y - (c + A x')‖ := by
        rw [hdiff, dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, hsub, sub_self, hzero,
          sub_sub]
  -- (iv)
  · rw [hdiff, LinearIsometryEquiv.norm_map]
    exact hle x' (y - c)
  -- (v)
  · rw [LinearIsometryEquiv.norm_map, hzero]
/-- Sup bound for the height of `spt V` over a graph plane, from a sup bound for the graph and a
lower density bound (a step of the proof of Simon Ch. 5, Theorem 4.5, p. 116; the missing-ball
argument is the one in the proofs of Lemma 2.6 and Corollary 2.7, pp. 112–113).  Let
`τ = q(0, c)`, `S = q(graph A)`, `λ(x') = c + A x'`, `Γ = q(graph f|B̄ⁿ_R(0))`, and let `b ≥ 0`,
`κ > 0`, `r + s₀ ≤ a`, `|c| + r + s₀ ≤ R`.  If `|f − λ| ≤ b` on `B̄ⁿ_a(0)`,
`μ_V(B̄_R(0) ∩ (spt V \ Γ)) ≤ β`, and `μ_V(B̄_s(x)) ≥ κ s` and `dist(x − τ, S) ≤ 2 s₀` for all
`x ∈ spt V ∩ B̄_r(τ)` and `s ∈ (0, s₀]`, then `dist(x − τ, S) ≤ max{2b, 2β/κ}` on `spt V ∩ B̄_r(τ)`.
Since `spt V` is `μ_V`-conull, it suffices that if `h = dist(x − τ, S) > 2b`, then the ball
`B̄_{h/2}(x)` lies in `B̄_R(0)` and misses `Γ`.  A point `y = q(y', f y')` of `Γ` in that ball has
`|y'| ≤ |y − τ| ≤ s₀ + r ≤ a`, hence `dist(y − τ, S) ≤ |f y' − λ(y')| ≤ b < h/2`.  This contradicts
`h ≤ dist(y − τ, S) + |x − y|`.  So `κ h/2 ≤ μ_V(B̄_{h/2}(x)) ≤ β`. -/
theorem tdo_graph_height_sup : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (c : Rn ℓ) (A : Rn n →L[ℝ] Rn ℓ) (R a r s₀ b β κ : ℝ), 0 ≤ b → 0 < κ → r + s₀ ≤ a → ‖c‖ + r + s₀ ≤ R → (∀ x' ∈ closedBall (0 : Rn n) a, ‖f x' - (c + A x')‖ ≤ b) → V.weight (closedBall 0 R ∩ (V.support \ q '' graphOver f (closedBall 0 R))) ≤ ENNReal.ofReal β → (∀ x ∈ V.support ∩ closedBall (q (graphPoint (0 : Rn n) c)) r, ∀ s : ℝ, 0 < s → s ≤ s₀ → ENNReal.ofReal (κ * s) ≤ V.weight (closedBall x s)) → (∀ x ∈ V.support ∩ closedBall (q (graphPoint (0 : Rn n) c)) r, infDist (x - q (graphPoint (0 : Rn n) c)) (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) : Set (Amb n ℓ)) ≤ 2 * s₀) → ∀ x ∈ V.support ∩ closedBall (q (graphPoint (0 : Rn n) c)) r, infDist (x - q (graphPoint (0 : Rn n) c)) (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) : Set (Amb n ℓ)) ≤ max (2 * b) (2 * β / κ) := by
  intro n ℓ U V q f c A R a r s₀ b β κ hb hκ hra hR hf hβ hdens hh x hx
  -- (iii) `dist(q(x', y) − τ, S) ≤ |y − λ(x')|`, (iv) `|x'| ≤ |q(x', y) − τ|` and (v) `|τ| = |c|`
  -- from the graph-plane distance estimates, at our `c`
  obtain ⟨-, -, hiii, hiv, hv⟩ := Submission.tdo_graph_plane_dist n ℓ q A
  have hiii := fun x' y => hiii x' y c
  have hiv := fun x' y => hiv x' y c
  have hv := hv c
  set τ := q (graphPoint (0 : Rn n) c)
  set S : Set (Amb n ℓ) :=
    (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) : Set (Amb n ℓ))
  set Γ := q '' graphOver f (closedBall (0 : Rn n) R)
  -- Step 1: `μ_V` is carried by `M ⊆ U` and by `spt μ_V`, so `μ_V((spt V)ᶜ) = 0`
  have hnull : V.weight V.supportᶜ = 0 := by
    have hM : (μHE[n] : Measure (Amb n ℓ)).restrict V.carrier V.carrierᶜ = 0 :=
      ae_iff.1 (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
    have hU : V.weight Uᶜ = 0 := withDensity_absolutelyContinuous _ _
      (measure_mono_null (compl_subset_compl.2 V.carrier_subset) hM)
    rw [RectifiableVarifold.support, compl_inter]
    exact measure_union_null hU Measure.measure_compl_support
  -- Step 2: we may assume `h = dist(x − τ, S) > 2b`; then `h/2 ∈ (b, s₀]`
  rcases le_or_gt (infDist (x - τ) S) (2 * b) with hle | hgt
  · exact le_max_of_le_left hle
  set h := infDist (x - τ) S
  have hh2 : h ≤ 2 * s₀ := hh x hx
  have hs : 0 < h / 2 := by linarith
  have hss₀ : h / 2 ≤ s₀ := by linarith
  have hbs : b < h / 2 := by linarith
  have hxτ : dist x τ ≤ r := mem_closedBall.1 hx.2
  -- Steps 3–5: `B̄_{h/2}(x) ⊆ B̄_R(0) \ Γ` (step 3, `x ∉ Γ`, is the case `z = x`)
  have hball : closedBall x (h / 2) ⊆ closedBall 0 R \ Γ := by
    intro z hz
    rw [mem_closedBall] at hz
    refine ⟨?_, ?_⟩
    · -- `|z| ≤ |z − x| + |x − τ| + |τ| ≤ s₀ + r + |c| ≤ R`
      have h4 := dist_triangle4 z x τ 0
      rw [dist_zero_right τ, hv] at h4
      rw [mem_closedBall]
      linarith
    · -- a point `y = q(y', f y')` of `Γ` in the ball would have `dist(y − τ, S) ≤ b < h/2`, while
      -- `dist(· − τ, S)` is `1`-Lipschitz and `|x − y| ≤ h/2`
      rintro ⟨w, ⟨y', -, rfl⟩, rfl⟩
      have hy' : ‖y'‖ ≤ a := by
        have h1 := hiv y' (f y')
        rw [← dist_eq_norm] at h1
        linarith [dist_triangle (q (graphPoint y' (f y'))) x τ]
      have hL : h ≤ infDist (q (graphPoint y' (f y')) - τ) S +
          dist (x - τ) (q (graphPoint y' (f y')) - τ) := infDist_le_infDist_add_dist
      rw [dist_sub_right, dist_comm] at hL
      linarith [hiii y' (f y'), hf y' (mem_closedBall_zero_iff.2 hy')]
  -- Step 6: `κ h/2 ≤ μ_V(B̄_{h/2}(x)) ≤ μ_V(B̄_R(0) ∩ (spt V \ Γ)) ≤ β`
  have hmass : ENNReal.ofReal (κ * (h / 2)) ≤ ENNReal.ofReal β :=
    calc ENNReal.ofReal (κ * (h / 2)) ≤ V.weight (closedBall x (h / 2)) := hdens x hx _ hs hss₀
      _ = V.weight (closedBall x (h / 2) ∩ V.support) := (measure_inter_conull hnull).symm
      _ ≤ V.weight (closedBall 0 R ∩ (V.support \ Γ)) :=
          measure_mono fun z hz => ⟨(hball hz.1).1, hz.2, (hball hz.1).2⟩
      _ ≤ ENNReal.ofReal β := hβ
  have hκβ : κ * (h / 2) ≤ β :=
    (ENNReal.ofReal_le_ofReal_iff'.1 hmass).resolve_right (not_le.2 (mul_pos hκ hs))
  refine le_max_of_le_right ((le_div_iff₀ hκ).2 ?_)
  linarith

/-- Simon Ch. 5, proof of Theorem 5.2, (10)–(11): for `f` `1`-Lipschitz on `D ⊆ ℝⁿ` and a linear
isometry `q` of `ℝ^{n+ℓ}`, the graph map `F(x) = q(x, f(x))` is `√2`-Lipschitz on `D`, and
`|F(x)| ≤ √2 |x|` on `D` when `f(0) = 0` and `0 ∈ D`. By the graph coordinates
(`lip_approx_graph_coordinates` (i), (ii)) and since `q` is a linear isometry,
`|F(x) − F(x')|² = |x − x'|² + |f(x) − f(x')|² ≤ 2 |x − x'|²`; and `F(0) = q(0, 0) = 0`. -/
theorem allard52_cft_graph_map_sqrt_two : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (D : Set (Rn n)), LipschitzOnWith 1 f D → (∀ x ∈ D, ∀ x' ∈ D, ‖q (graphPoint x (f x)) - q (graphPoint x' (f x'))‖ ≤ Real.sqrt 2 * ‖x - x'‖) ∧ (f 0 = 0 → (0 : Rn n) ∈ D → ∀ x ∈ D, ‖q (graphPoint x (f x))‖ ≤ Real.sqrt 2 * ‖x‖) := by
  intro n ℓ q f D hf
  obtain ⟨hsub, hnorm, -, -⟩ := lip_approx_graph_coordinates n ℓ q
  have hlip : ∀ x ∈ D, ∀ x' ∈ D,
      ‖q (graphPoint x (f x)) - q (graphPoint x' (f x'))‖ ≤ Real.sqrt 2 * ‖x - x'‖ := by
    intro x hx x' hx'
    -- `|f(x) − f(x')| ≤ |x − x'|`
    have hf' : ‖f x - f x'‖ ≤ ‖x - x'‖ := by
      have h := hf.dist_le_mul x hx x' hx'
      rwa [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at h
    -- `|F(x) − F(x')| = |(x − x', f(x) − f(x'))|`, whose square is at most `2 |x − x'|²`
    rw [← map_sub, q.norm_map, hsub]
    have hsq : ‖graphPoint (x - x') (f x - f x')‖ ^ 2 ≤ (Real.sqrt 2 * ‖x - x'‖) ^ 2 := by
      rw [hnorm, mul_pow, Real.sq_sqrt zero_le_two, two_mul]
      exact add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hf' 2)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) two_ne_zero).mp hsq
  refine ⟨hlip, fun hf0 h0 x hx => ?_⟩
  -- `(0, 0) = (0, 0) − (0, 0) = 0`, so `F(0) = 0`; compare `F(x)` with `F(0)`
  have hzero : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    have h := hsub 0 0 0 0
    rw [sub_self, sub_self, sub_self] at h
    exact h.symm
  have h := hlip x hx 0 h0
  rwa [hf0, hzero, map_zero, sub_zero, sub_zero] at h

/-- Simon Ch. 5, proof of Theorem 4.5 (pp. 116–120), integrals over the Lipschitz graph: for a
linear isometry `q` of `ℝ^{n+ℓ}` and `f : ℝⁿ → ℝ^ℓ` that is `L`-Lipschitz on `D`, the map
`F(x) = q(x, f(x))` is `√(1 + L²)`-Lipschitz on `D`.  Since `q` preserves distances and
`|(x, f x) − (y, f y)|² = |x − y|² + |f(x) − f(y)|²` (split the sum `Σ_k w_k²` over the indices
`castAdd ℓ i` and `natAdd n j` of `Fin (n + ℓ)` with `Fin.sum_univ_add`), the hypothesis gives
`|F(x) − F(y)|² ≤ (1 + L²)|x − y|² = (√(1 + L²) |x − y|)²` for `x, y ∈ D`; take square roots. -/
theorem tdo_gl_graph_map_lipschitzOn : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (D : Set (Rn n)) (L : ℝ≥0), LipschitzOnWith L f D → LipschitzOnWith (NNReal.sqrt (1 + L ^ 2)) (fun x => q (graphPoint x (f x))) D := by
  intro n ℓ q f D L hf
  -- the coordinates of `graphPoint a b`
  have hl : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp [graphPoint]
  have hr : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp [graphPoint]
  -- `|(a, b) − (a', b')|² = |a − a'|² + |b − b'|²`, splitting `Σ_k w_k²` over the two blocks
  have hsq : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      ‖graphPoint a b - graphPoint a' b'‖ ^ 2 = ‖a - a'‖ ^ 2 + ‖b - b'‖ ^ 2 := by
    intro a a' b b'
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp only [PiLp.sub_apply, hl, hr]
  -- `q` preserves distances, so it suffices to bound `|(x, f x) − (y, f y)|` by
  -- `√(1 + L²) |x − y|` for `x, y ∈ D`
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [LinearIsometryEquiv.dist_map, dist_eq_norm, dist_eq_norm, Real.coe_sqrt, NNReal.coe_add,
    NNReal.coe_one, NNReal.coe_pow]
  -- `|f x − f y|² ≤ L² |x − y|²` on `D`
  have hfxy : ‖f x - f y‖ ^ 2 ≤ (L * ‖x - y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hf.norm_sub_le hx hy) 2
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [hsq, mul_pow, Real.sq_sqrt (by positivity)]
  rw [mul_pow] at hfxy
  linarith
/-- Simon Ch. 5, proof of Theorem 4.5 (pp. 116–120), integrals over a Lipschitz image: if
`F : ℝⁿ → ℝ^N` is `K`-Lipschitz on the measurable set `D`, then for measurable `g ≥ 0`
`∫_{F(D)} g dHⁿ ≤ Kⁿ ∫_D g(F(x')) dx'`.  For `E ⊆ D` the image bound gives
`Hⁿ(F(E)) ≤ Kⁿ Hⁿ(E) = Kⁿ Lⁿ(E)`.  With `ν = F_#(Lⁿ ⌞ D)` (`F` is continuous on `D`, hence
a.e. measurable for `Lⁿ ⌞ D`) and `B ∩ F(D) = F(F⁻¹(B) ∩ D)`, this gives
`(Hⁿ ⌞ F(D))(B) ≤ Kⁿ ν(B)` for measurable `B`, i.e. `Hⁿ ⌞ F(D) ≤ Kⁿ ν`; integrate `g` and
change variables. -/
theorem tdo_gl_lintegral_image_le : ∀ (n N : ℕ) (F : Rn n → EuclideanSpace ℝ (Fin N)) (D : Set (Rn n)) (K : ℝ≥0), MeasurableSet D → LipschitzOnWith K F D → ∀ g : EuclideanSpace ℝ (Fin N) → ℝ≥0∞, Measurable g → ∫⁻ x in F '' D, g x ∂(μHE[n] : Measure (EuclideanSpace ℝ (Fin N))) ≤ (K : ℝ≥0∞) ^ n * ∫⁻ x' in D, g (F x') := by
  intro n N F D K hD hF g hg
  -- `F` is continuous on the measurable set `D`, hence a.e. measurable for `Lⁿ ⌞ D`
  have hFm : AEMeasurable F ((volume : Measure (Rn n)).restrict D) :=
    hF.continuousOn.aemeasurable hD
  -- `Hⁿ ⌞ F(D) ≤ Kⁿ F_#(Lⁿ ⌞ D)`, tested on measurable `B` via `B ∩ F(D) = F(F⁻¹(B) ∩ D)`
  have hle : (μHE[n] : Measure (EuclideanSpace ℝ (Fin N))).restrict (F '' D) ≤
      ((K : ℝ≥0∞) ^ n) • Measure.map F ((volume : Measure (Rn n)).restrict D) := by
    refine Measure.le_iff.2 fun B hB => ?_
    rw [Measure.restrict_apply hB, Measure.smul_apply, Measure.map_apply_of_aemeasurable hFm hB,
      Measure.restrict_apply' hD, smul_eq_mul]
    have hset : B ∩ F '' D = F '' (F ⁻¹' B ∩ D) := by
      ext y
      constructor
      · rintro ⟨hyB, x, hxD, rfl⟩
        exact ⟨x, ⟨hyB, hxD⟩, rfl⟩
      · rintro ⟨x, ⟨hxB, hxD⟩, rfl⟩
        exact ⟨hxB, x, hxD, rfl⟩
    rw [hset, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
    exact Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hF.mono Set.inter_subset_right)
  calc ∫⁻ x in F '' D, g x ∂(μHE[n] : Measure (EuclideanSpace ℝ (Fin N)))
      ≤ ∫⁻ x, g x ∂(((K : ℝ≥0∞) ^ n) • Measure.map F ((volume : Measure (Rn n)).restrict D)) :=
        lintegral_mono' hle le_rfl
    _ = (K : ℝ≥0∞) ^ n * ∫⁻ x, g x ∂(Measure.map F ((volume : Measure (Rn n)).restrict D)) := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ = (K : ℝ≥0∞) ^ n * ∫⁻ x' in D, g (F x') := by
        rw [lintegral_map' hg.aemeasurable hFm]
/-- **Simon Ch. 5, proof of Theorem 4.5, display (14) on p. 119** (the area-formula step, Ch. 2,
3.5, with `JF ≤ (1 + L²)^{n/2}`).  Let `q` be a linear isometry of `ℝ^{n+ℓ}`, `D ⊆ ℝⁿ` measurable
and `f` `L`-Lipschitz on `D`, and put `F x' = q (x', f x')`.  Then for every measurable `g ≥ 0`,
`∫_{q(graph f|D)} g dHⁿ ≤ √(1 + L²)ⁿ ∫_D g ∘ F dLⁿ`.  Indeed `q(graph f|D) = F(D)`, `F` is
`√(1 + L²)`-Lipschitz on `D`, and the Lipschitz image bound for `Hⁿ`-integrals applies with
`K = √(1 + L²)`. -/
theorem tdo_graph_lintegral_le : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (D : Set (Rn n)) (L : ℝ≥0), MeasurableSet D → LipschitzOnWith L f D → ∀ g : Amb n ℓ → ℝ≥0∞, Measurable g → ∫⁻ x in q '' graphOver f D, g x ∂(μHE[n] : Measure (Amb n ℓ)) ≤ ENNReal.ofReal (Real.sqrt (1 + (L : ℝ) ^ 2) ^ n) * ∫⁻ x' in D, g (q (graphPoint x' (f x'))) := by
  intro n ℓ q f D L hD hf g hg
  -- Step (i): `q(graph f|D) = F(D)` for the rotated graph map `F x' = q (x', f x')`.
  have hΓ : q '' graphOver f D = (fun x' => q (graphPoint x' (f x'))) '' D := by
    rw [graphOver, Set.image_image]
  -- Step (ii): `F` is `√(1 + L²)`-Lipschitz on `D`.
  have hF := Submission.tdo_gl_graph_map_lipschitzOn n ℓ q f D L hf
  -- Step (iv): the constant `√(1 + L²)ⁿ`, as the `n`-th power of `K = √(1 + L²) ∈ ℝ≥0`.
  have hK : ENNReal.ofReal (Real.sqrt (1 + (L : ℝ) ^ 2) ^ n) =
      ((NNReal.sqrt (1 + L ^ 2) : ℝ≥0) : ℝ≥0∞) ^ n := by
    rw [ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt,
      NNReal.coe_add, NNReal.coe_one, NNReal.coe_pow]
  rw [hΓ, hK]
  -- Step (iii): the Lipschitz image bound with `N = n + ℓ` and `K = √(1 + L²)`.
  exact Submission.tdo_gl_lintegral_image_le n (n + ℓ) _ D _ hD hF g hg
/-- Integrals over the open ball `B̆_a(0)` of `ℝ¹` are integrals over the interval `(-a, a)`, for
every function `φ` and every radius `a` (no integrability hypothesis).  The coordinate map
`e := toLp 2 ∘ (funUnique (Fin 1) ℝ).symm : ℝ ≃ᵐ ℝ¹` sends `t` to `EuclideanSpace.single 0 t` and is
volume preserving (`volume_preserving_funUnique`, `PiLp.volume_preserving_toLp`), so
`MeasurePreserving.setIntegral_preimage_emb` transfers the integral; the preimage of the ball is
`{t | |t| < a} = Ioo (-a) a` since `‖single 0 t‖ = |t|` (`PiLp.norm_single`). -/
theorem tdo_ods_ball_integral_eq_interval : ∀ (φ : Rn 1 → ℝ) (a : ℝ),
    (∫ y in ball (0 : Rn 1) a, φ y) =
      ∫ t in Ioo (-a) a, φ (EuclideanSpace.single (0 : Fin 1) t) := by
  intro φ a
  set e : ℝ ≃ᵐ Rn 1 :=
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.trans (MeasurableEquiv.toLp 2 (Fin 1 → ℝ))
  have he : ∀ t, e t = EuclideanSpace.single (0 : Fin 1) t := by
    intro t
    ext i
    fin_cases i
    simp [e]
  have hmp : MeasurePreserving e volume volume :=
    (PiLp.volume_preserving_toLp (Fin 1)).comp (volume_preserving_funUnique (Fin 1) ℝ).symm
  have hpre : e ⁻¹' ball (0 : Rn 1) a = Ioo (-a) a := by
    ext t
    simp [he, abs_lt]
  rw [← hmp.setIntegral_preimage_emb e.measurableEmbedding φ (ball 0 a), hpre]
  simp_rw [he]
/-- On `ℝ¹` the squared Hilbert–Schmidt norm of `Dw` at `single 0 t` is the squared norm of the
derivative of `s ↦ w (single 0 s)` at `t`, for every map `w` (Mathlib's `fderiv`/`deriv` vanish at
points of non-differentiability).  `hsNormSq B = ‖B e‖²` with `e := single 0 1` (`Fin 1` is a
singleton) and `single 0 s = s • e`.  If `w` is differentiable at `single 0 t`, the chain rule
(`HasFDerivAt.comp_hasDerivAt`) gives `deriv (w ∘ single 0) t = Dw(single 0 t) e`.  Otherwise
`w ∘ single 0` is not differentiable at `t` either, since `w = (w ∘ single 0) ∘ π` for the
coordinate projection `π := EuclideanSpace.proj 0`, so both sides vanish. -/
theorem tdo_ods_hsNormSq_fderiv_single : ∀ (ℓ : ℕ) (w : Rn 1 → Rn ℓ) (t : ℝ),
    hsNormSq (fderiv ℝ w (EuclideanSpace.single (0 : Fin 1) t)) =
      ‖deriv (fun s : ℝ => w (EuclideanSpace.single (0 : Fin 1) s)) t‖ ^ 2 := by
  intro ℓ w t
  set e : Rn 1 := EuclideanSpace.single (0 : Fin 1) (1 : ℝ)
  have hsing : ∀ s : ℝ, EuclideanSpace.single (0 : Fin 1) s = s • e := by
    intro s
    ext i
    fin_cases i
    simp [e]
  have hLHS : hsNormSq (fderiv ℝ w (EuclideanSpace.single (0 : Fin 1) t)) =
      ‖fderiv ℝ w (EuclideanSpace.single (0 : Fin 1) t) e‖ ^ 2 := by
    simp [hsNormSq, e]
  rw [hLHS]
  by_cases hw : DifferentiableAt ℝ w (EuclideanSpace.single (0 : Fin 1) t)
  · have hι : HasDerivAt (fun s : ℝ => EuclideanSpace.single (0 : Fin 1) s) e t := by
      simpa [hsing] using (hasDerivAt_id t).smul_const e
    have hW : HasDerivAt (fun s : ℝ => w (EuclideanSpace.single (0 : Fin 1) s))
        (fderiv ℝ w (EuclideanSpace.single (0 : Fin 1) t) e) t :=
      hw.hasFDerivAt.comp_hasDerivAt t hι
    rw [hW.deriv]
  · have hW : ¬ DifferentiableAt ℝ (fun s : ℝ => w (EuclideanSpace.single (0 : Fin 1) s)) t := by
      intro hW
      apply hw
      set π : Rn 1 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 1)
      have hπt : π (EuclideanSpace.single (0 : Fin 1) t) = t := by simp [π]
      have hcomp := DifferentiableAt.comp (EuclideanSpace.single (0 : Fin 1) t)
        (by rw [hπt]; exact hW) π.differentiableAt
      have hw_eq : ((fun s : ℝ => w (EuclideanSpace.single (0 : Fin 1) s)) ∘ π) = w := by
        funext z
        simp only [Function.comp_apply]
        congr 1
        ext i
        fin_cases i
        simp [π]
      rwa [hw_eq] at hcomp
    rw [fderiv_zero_of_not_differentiableAt hw, deriv_zero_of_not_differentiableAt hW]
    simp
/-- **Integrability of `‖W'‖` for a Lipschitz curve.**  If `W : ℝ → ℝ^ℓ` is `K`-Lipschitz on
`[-a, a]`, then `r ↦ ‖deriv W r‖` is integrable on `(-a, a)`: it is measurable
(`measurable_deriv`), bounded by `K` on `(-a, a)` because `[-a, a]` is a neighbourhood of each
point there (`norm_deriv_le_of_lipschitzOn`), and `(-a, a)` has finite measure. -/
theorem Submission.tdo_ods_integrableOn_norm_deriv : ∀ (ℓ : ℕ) (W : ℝ → Rn ℓ) (a : ℝ) (K : ℝ≥0), LipschitzOnWith K W (Icc (-a) a) → IntegrableOn (fun r => ‖deriv W r‖) (Ioo (-a) a) := by
  intro ℓ W a K hW
  -- (1) measurability of `‖W'‖`, (4) finite measure of `(-a, a)`
  refine Measure.integrableOn_of_bounded (M := K) measure_Ioo_lt_top.ne
    (measurable_deriv W).norm.aestronglyMeasurable ?_
  -- (3) the a.e. bound on `(-a, a)` follows from the pointwise one
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Filter.Eventually.of_forall fun r hr => ?_
  -- (2) `[-a, a]` is a neighbourhood of `r ∈ (-a, a)`, so `‖W'(r)‖ ≤ K`
  rw [norm_norm]
  exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr.1 hr.2) hW


/-- A.e. derivative comparison for the one-dimensional sup bound in the tilt-excess decay
(Simon Ch. 5, Theorem 4.5): if `W : ℝ → ℝ^ℓ` is `K`-Lipschitz on `[-a, a]` and `‖u‖ ≤ 1`, then
`|(d/dr)⟨u, W(r)⟩| ≤ ‖W'(r)‖` for a.e. `r ∈ (-a, a)`.  By Rademacher's theorem `W` is
differentiable within `[-a, a]` at a.e. point of `[-a, a]`, hence differentiable at a.e.
`r ∈ (-a, a)`, where `[-a, a]` is a neighbourhood of `r`; there `x ↦ ⟨u, W x⟩` has derivative
`⟨u, W'(r)⟩`, and Cauchy–Schwarz with `‖u‖ ≤ 1` gives the bound. -/
theorem tdo_ods_ae_abs_deriv_inner_le : ∀ (ℓ : ℕ) (W : ℝ → Rn ℓ) (a : ℝ) (K : ℝ≥0) (u : Rn ℓ), LipschitzOnWith K W (Icc (-a) a) → ‖u‖ ≤ 1 → ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (-a) a → |deriv (fun x => inner ℝ u (W x)) r| ≤ ‖deriv W r‖ := by
  intro ℓ W a K u hW hu
  -- Step 1 (Rademacher): for a.e. `r ∈ [-a, a]`, `W` is differentiable within `[-a, a]` at `r`.
  filter_upwards [hW.ae_differentiableWithinAt_of_mem (μ := volume)] with r hr hrI
  -- Step 2: for `r ∈ (-a, a)`, `[-a, a]` is a neighbourhood of `r`, so `W` is differentiable at `r`.
  have hWr : DifferentiableAt ℝ W r :=
    (hr (Ioo_subset_Icc_self hrI)).differentiableAt (Icc_mem_nhds hrI.1 hrI.2)
  -- Step 3: `x ↦ ⟨u, W x⟩` has derivative `⟨u, W'(r)⟩ + ⟨0, W r⟩ = ⟨u, W'(r)⟩` at `r`.
  have hd : HasDerivAt (fun x => inner ℝ u (W x)) (inner ℝ u (deriv W r)) r := by
    simpa using (hasDerivAt_const r u).inner ℝ hWr.hasDerivAt
  rw [hd.deriv]
  -- Step 4: Cauchy–Schwarz and `‖u‖ ≤ 1`.
  calc |inner ℝ u (deriv W r)| ≤ ‖u‖ * ‖deriv W r‖ := abs_real_inner_le_norm u (deriv W r)
    _ ≤ 1 * ‖deriv W r‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
    _ = ‖deriv W r‖ := one_mul _

end Submission

namespace Submission

/-- Interval integral bounded by an a.e. dominating function, for the FTC bound in the
one-dimensional sup estimate of the tilt-excess decay (Simon Ch. 5, Theorem 4.5): if `h` is
integrable on `(-a, a)`, `s, t ∈ [-a, a]`, `g` is interval integrable between `s` and `t` and
`|g| ≤ h` a.e. on `(-a, a)`, then `∫_s^t g ≤ ∫_{(-a,a)} h`.  Since `uIoc s t ⊆ (-a, a]` and the
endpoint `a` is Lebesgue-null,
`∫_s^t g ≤ ‖∫_s^t g‖ ≤ ∫_{uIoc s t} ‖g‖ ≤ ∫_{uIoc s t} h ≤ ∫_{(-a,a]} h = ∫_{(-a,a)} h`,
where the fourth step uses `0 ≤ |g| ≤ h` a.e. on `(-a, a]`. -/
theorem tdo_ods_intervalIntegral_le_of_ae_abs_le : ∀ (g h : ℝ → ℝ) (a s t : ℝ), IntegrableOn h (Ioo (-a) a) → s ∈ Icc (-a) a → t ∈ Icc (-a) a → IntervalIntegrable g volume s t → (∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (-a) a → |g r| ≤ h r) → ∫ r in s..t, g r ≤ ∫ r in Ioo (-a) a, h r := by
  intro g h a s t hh hs ht hg hgh
  -- Step 1: `uIoc s t ⊆ (-a, a]`, since `s, t ∈ [-a, a]`.
  have hsub : uIoc s t ⊆ Ioc (-a) a := by
    intro r hr
    rcases mem_uIoc.1 hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hs.1.trans_lt h1, h2.trans ht.2⟩
    · exact ⟨ht.1.trans_lt h1, h2.trans hs.2⟩
  -- Step 2: `h` is integrable on `(-a, a]` (the endpoint `a` is null and `h a` is finite),
  -- hence on `uIoc s t`.
  have hhIoc : IntegrableOn h (Ioc (-a) a) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top).2 hh
  have hhI : IntegrableOn h (uIoc s t) := hhIoc.mono_set hsub
  -- Step 3: `‖g‖` is integrable on `uIoc s t`.
  have hgI : IntegrableOn (fun r => ‖g r‖) (uIoc s t) := (intervalIntegrable_iff.1 hg).norm
  -- Step 4: `|g| ≤ h` a.e. on `(-a, a]` (a.e. `r ≠ a`), hence `0 ≤ h` a.e. there.
  have hdom : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioc (-a) a → |g r| ≤ h r := by
    filter_upwards [hgh, Measure.ae_ne volume a] with r hr hra hrI
    exact hr ⟨hrI.1, lt_of_le_of_ne hrI.2 hra⟩
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (-a) a)] h := by
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hdom] with r hr hrI
    exact (abs_nonneg _).trans (hr hrI)
  -- Step 5: the chain of inequalities.
  calc ∫ r in s..t, g r ≤ ‖∫ r in s..t, g r‖ := Real.le_norm_self _
    _ ≤ ∫ r in uIoc s t, ‖g r‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ r in uIoc s t, h r := by
        refine setIntegral_mono_on_ae hgI hhI measurableSet_uIoc ?_
        filter_upwards [hdom] with r hr hrI
        rw [Real.norm_eq_abs]
        exact hr (hsub hrI)
    _ ≤ ∫ r in Ioc (-a) a, h r := setIntegral_mono_set hhIoc hnonneg (ae_of_all _ hsub)
    _ = ∫ r in Ioo (-a) a, h r := integral_Ioc_eq_integral_Ioo

end Submission

namespace Submission

/-- **FTC bound for a Lipschitz curve** (used for the one-dimensional sup bound in the proof of the
Tilt-excess Decay Theorem, Simon Ch. 5, 4.5).  If `W : ℝ → ℝ^ℓ` is `K`-Lipschitz on `[-a, a]`, then
`|W(t) - W(s)| ≤ ∫_{(-a,a)} |W'|` for all `s, t ∈ [-a, a]`.

Proof: if `W(t) = W(s)` the right side is the integral of a nonnegative function.  Otherwise put
`v = W(t) - W(s)` and `u = |v|⁻¹ v`, so `|u| = 1` and `⟨u, v⟩ = |v|`.  The scalar function
`φ = ⟨u, W⟩` is `K`-Lipschitz on `[-a, a] ⊇ uIcc s t`, hence absolutely continuous there, so
`|v| = φ(t) - φ(s) = ∫_s^t φ'` (`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`) and `φ'` is
interval integrable.  Since `|W'|` is integrable on `(-a, a)` (`tdo_ods_integrableOn_norm_deriv`)
and `|φ'| ≤ |W'|` a.e. on `(-a, a)` (`tdo_ods_ae_abs_deriv_inner_le`), the dominated interval
bound `tdo_ods_intervalIntegral_le_of_ae_abs_le` gives `∫_s^t φ' ≤ ∫_{(-a,a)} |W'|`. -/
theorem tdo_ods_norm_sub_le_integral_deriv : ∀ (ℓ : ℕ) (W : ℝ → Rn ℓ) (a : ℝ) (K : ℝ≥0), LipschitzOnWith K W (Icc (-a) a) → ∀ s ∈ Icc (-a) a, ∀ t ∈ Icc (-a) a, ‖W t - W s‖ ≤ ∫ r in Ioo (-a) a, ‖deriv W r‖ := by
  intro ℓ W a K hW s hs t ht
  -- The trivial case `W t = W s`: the integrand is nonnegative.
  by_cases hv : W t - W s = 0
  · rw [hv, norm_zero]
    exact integral_nonneg fun r => norm_nonneg _
  -- The unit vector `u = |v|⁻¹ v` for `v = W t - W s`.
  have hvn : ‖W t - W s‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  set u : Rn ℓ := ‖W t - W s‖⁻¹ • (W t - W s) with hu_def
  have hu : ‖u‖ ≤ 1 := by
    have h1 : ‖u‖ = 1 := by rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn]
    exact h1.le
  -- `φ = ⟨u, W⟩` is `K`-Lipschitz on `[-a, a]`, hence absolutely continuous on `uIcc s t`.
  set φ : ℝ → ℝ := fun x => inner ℝ u (W x) with hφ_def
  have hφ : LipschitzOnWith K φ (Icc (-a) a) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    calc dist (φ x) (φ y) = |inner ℝ u (W x - W y)| := by
          rw [Real.dist_eq, inner_sub_right]
      _ ≤ ‖u‖ * ‖W x - W y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖W x - W y‖ := mul_le_of_le_one_left (norm_nonneg _) hu
      _ = dist (W x) (W y) := (dist_eq_norm _ _).symm
      _ ≤ K * dist x y := hW.dist_le_mul x hx y hy
  have hac := (hφ.mono (uIcc_subset_Icc hs ht)).absolutelyContinuousOnInterval
  -- `φ(t) - φ(s) = ⟨u, v⟩ = |v|`.
  have hφst : φ t - φ s = ‖W t - W s‖ := by
    show inner ℝ u (W t) - inner ℝ u (W s) = ‖W t - W s‖
    rw [← inner_sub_right, hu_def, real_inner_smul_left, real_inner_self_eq_norm_sq, sq,
      ← mul_assoc, inv_mul_cancel₀ hvn, one_mul]
  calc ‖W t - W s‖ = φ t - φ s := hφst.symm
    _ = ∫ r in s..t, deriv φ r := hac.integral_deriv_eq_sub.symm
    _ ≤ ∫ r in Ioo (-a) a, ‖deriv W r‖ :=
      Submission.tdo_ods_intervalIntegral_le_of_ae_abs_le (deriv φ) (fun r => ‖deriv W r‖) a s t
        (Submission.tdo_ods_integrableOn_norm_deriv ℓ W a K hW) hs ht hac.intervalIntegrable_deriv
        (Submission.tdo_ods_ae_abs_deriv_inner_le ℓ W a K u hW hu)

/-- Cauchy–Schwarz on `(-a, a)`: `∫_{(-a,a)} g ≤ √(2a ∫_{(-a,a)} g²)`.  If `g` is not integrable on
`(-a, a)`, the left side is `0` (`integral_undef`).  Otherwise put `I := ∫ g²`, `J := ∫ |g|` and
`m := J / (2a)`.  Then `∫ g ≤ J` (`integral_mono`), the measure of `(-a, a)` is `2a`
(`Real.volume_real_Ioo_of_le`), and the variance identity
`0 ≤ ∫ (|g| - m)² = I - 2mJ + 2a m² = I - J² / (2a)` gives `J² ≤ 2a I`, so
`J ≤ |J| ≤ √(2a I)` (`Real.abs_le_sqrt`). -/
theorem tdo_ods_integral_le_sqrt : ∀ (g : ℝ → ℝ) (a : ℝ), 0 < a →
    IntegrableOn (fun s => g s ^ 2) (Ioo (-a) a) →
    (∫ s in Ioo (-a) a, g s) ≤ Real.sqrt (2 * a * ∫ s in Ioo (-a) a, g s ^ 2) := by
  intro g a ha hg2
  by_cases hg : IntegrableOn g (Ioo (-a) a)
  swap
  · rw [integral_undef hg]
    exact Real.sqrt_nonneg _
  set I := ∫ s in Ioo (-a) a, g s ^ 2
  set J := ∫ s in Ioo (-a) a, |g s|
  have hgJ : (∫ s in Ioo (-a) a, g s) ≤ J :=
    integral_mono hg hg.abs fun s => le_abs_self (g s)
  have hvol : volume.real (Ioo (-a) a) = 2 * a := by
    rw [Real.volume_real_Ioo_of_le (by linarith)]; ring
  set m := J / (2 * a) with hm
  have hvar : ∫ s in Ioo (-a) a, (|g s| - m) ^ 2 = I - 2 * m * J + 2 * a * m ^ 2 := by
    have hpt : ∀ s, (|g s| - m) ^ 2 = (g s ^ 2 - 2 * m * |g s|) + m ^ 2 := by
      intro s; rw [sub_sq, sq_abs]; ring
    have hgm : IntegrableOn (fun s => 2 * m * |g s|) (Ioo (-a) a) := hg.abs.const_mul (2 * m)
    have hsub : IntegrableOn (fun s => g s ^ 2 - 2 * m * |g s|) (Ioo (-a) a) := hg2.sub hgm
    have hc : IntegrableOn (fun _ : ℝ => m ^ 2) (Ioo (-a) a) :=
      integrableOn_const measure_Ioo_lt_top.ne
    simp_rw [hpt]
    rw [integral_add hsub hc, integral_sub hg2 hgm, integral_const_mul, setIntegral_const, hvol,
      smul_eq_mul]
  have hnn : 0 ≤ ∫ s in Ioo (-a) a, (|g s| - m) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo fun s _ => sq_nonneg _
  have hJ2 : J ^ 2 ≤ 2 * a * I := by
    rw [hvar, hm] at hnn
    have h2a : (0 : ℝ) < 2 * a := by linarith
    have key : I - 2 * (J / (2 * a)) * J + 2 * a * (J / (2 * a)) ^ 2 = I - J ^ 2 / (2 * a) := by
      field_simp; ring
    rw [key, sub_nonneg, div_le_iff₀ h2a] at hnn
    linarith
  calc (∫ s in Ioo (-a) a, g s) ≤ J := hgJ
    _ ≤ |J| := le_abs_self J
    _ ≤ Real.sqrt (2 * a * I) := Real.abs_le_sqrt hJ2

end Submission
/-- One-dimensional sup bound (used for the one-dimensional sup estimate in the proof of the
Tilt-excess Decay Theorem, Simon Ch. 5, 4.5): if `W : ℝ → ℝ^ℓ` is `K`-Lipschitz on `[-a, a]`, then
for every `t ∈ [-a, a]`,
`|W(t)| ≤ ((2a)⁻¹ ∫_{(-a,a)} |W|²)^{1/2} + (2a ∫_{(-a,a)} |W'|²)^{1/2}`.

Proof: `|W|` and `|W|²` are continuous on `[-a, a]`, and `|W'|² ≤ K²` on `(-a, a)`
(`norm_deriv_le_of_lipschitzOn`), so all three integrands are integrable on `(-a, a)`.  By
`tdo_ods_norm_sub_le_integral_deriv`, `|W(t)| ≤ |W(s)| + D` for all `s ∈ (-a, a)`, where
`D = ∫_{(-a,a)} |W'|`; averaging over `s` gives `|W(t)| ≤ (2a)⁻¹ ∫_{(-a,a)} |W| + D`, and
`tdo_ods_integral_le_sqrt` (Cauchy–Schwarz) bounds `∫_{(-a,a)} |W|` and `D`. -/
theorem Submission.tdo_ods_interval_sup_le : ∀ (ℓ : ℕ) (W : ℝ → Rn ℓ) (a : ℝ) (K : ℝ≥0), 0 < a → LipschitzOnWith K W (Icc (-a) a) → ∀ t ∈ Icc (-a) a, ‖W t‖ ≤ Real.sqrt ((2 * a)⁻¹ * ∫ s in Ioo (-a) a, ‖W s‖ ^ 2) + Real.sqrt (2 * a * ∫ s in Ioo (-a) a, ‖deriv W s‖ ^ 2) := by
  intro ℓ W a K ha hW t ht
  have h2a : 0 < 2 * a := by linarith
  have hfin : volume (Ioo (-a) a) ≠ ∞ := measure_Ioo_lt_top.ne
  -- Step 1: `|W|` and `|W|²` are continuous on `[-a, a]`, hence integrable on `(-a, a)`.
  have hcont : ContinuousOn (fun s => ‖W s‖) (Icc (-a) a) := hW.continuousOn.norm
  have hW1 : IntegrableOn (fun s => ‖W s‖) (Ioo (-a) a) :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hW2 : IntegrableOn (fun s => ‖W s‖ ^ 2) (Ioo (-a) a) :=
    (hcont.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  -- Step 2: `deriv W` is measurable and `|W'|² ≤ K²` on `(-a, a)`.
  have hD2 : IntegrableOn (fun s => ‖deriv W s‖ ^ 2) (Ioo (-a) a) := by
    refine Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) hfin
      ((measurable_deriv W).norm.pow_const 2).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun r hr => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr.1 hr.2) hW) 2
  -- Step 3: `|W(t)| ≤ |W(s)| + D` for every `s ∈ (-a, a)`.
  set D := ∫ r in Ioo (-a) a, ‖deriv W r‖
  have hpt : ∀ s ∈ Ioo (-a) a, ‖W t‖ ≤ ‖W s‖ + D := fun s hs =>
    (norm_le_norm_add_norm_sub' (W t) (W s)).trans (add_le_add le_rfl
      (Submission.tdo_ods_norm_sub_le_integral_deriv ℓ W a K hW s (Ioo_subset_Icc_self hs) t ht))
  -- Step 4: average over `s ∈ (-a, a)`, an interval of length `2a`.
  have hvol : volume.real (Ioo (-a) a) = 2 * a := by
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring
  have hconst : IntegrableOn (fun _ : ℝ => ‖W t‖) (Ioo (-a) a) := integrableOn_const hfin
  have hconstD : IntegrableOn (fun _ : ℝ => D) (Ioo (-a) a) := integrableOn_const hfin
  have hsum : IntegrableOn (fun s => ‖W s‖ + D) (Ioo (-a) a) := hW1.add hconstD
  have havg : 2 * a * ‖W t‖ ≤ (∫ s in Ioo (-a) a, ‖W s‖) + 2 * a * D := by
    have h := setIntegral_mono_on hconst hsum measurableSet_Ioo hpt
    rwa [setIntegral_const, integral_add hW1 hconstD, setIntegral_const, hvol, smul_eq_mul,
      smul_eq_mul] at h
  have hinv : (2 * a)⁻¹ * (2 * a) = 1 := inv_mul_cancel₀ h2a.ne'
  have hmean : ‖W t‖ ≤ (2 * a)⁻¹ * (∫ s in Ioo (-a) a, ‖W s‖) + D :=
    calc ‖W t‖ = (2 * a)⁻¹ * (2 * a * ‖W t‖) := by rw [← mul_assoc, hinv, one_mul]
      _ ≤ (2 * a)⁻¹ * ((∫ s in Ioo (-a) a, ‖W s‖) + 2 * a * D) :=
        mul_le_mul_of_nonneg_left havg (inv_nonneg.2 h2a.le)
      _ = (2 * a)⁻¹ * (∫ s in Ioo (-a) a, ‖W s‖) + D := by
        rw [mul_add, ← mul_assoc, hinv, one_mul]
  -- Step 5: Cauchy–Schwarz for `|W|`.
  have hW_cs : (2 * a)⁻¹ * (∫ s in Ioo (-a) a, ‖W s‖) ≤
      Real.sqrt ((2 * a)⁻¹ * ∫ s in Ioo (-a) a, ‖W s‖ ^ 2) :=
    calc (2 * a)⁻¹ * (∫ s in Ioo (-a) a, ‖W s‖)
        ≤ (2 * a)⁻¹ * Real.sqrt (2 * a * ∫ s in Ioo (-a) a, ‖W s‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (Submission.tdo_ods_integral_le_sqrt (fun s => ‖W s‖) a ha hW2)
            (inv_nonneg.2 h2a.le)
      _ = Real.sqrt ((2 * a)⁻¹ ^ 2 * (2 * a * ∫ s in Ioo (-a) a, ‖W s‖ ^ 2)) := by
          rw [Real.sqrt_mul (sq_nonneg (2 * a)⁻¹), Real.sqrt_sq (inv_nonneg.2 h2a.le)]
      _ = Real.sqrt ((2 * a)⁻¹ * ∫ s in Ioo (-a) a, ‖W s‖ ^ 2) := by
          rw [sq, mul_assoc, ← mul_assoc (2 * a)⁻¹ (2 * a), hinv, one_mul]
  -- Step 6: Cauchy–Schwarz for `|W'|`.
  have hD_cs : D ≤ Real.sqrt (2 * a * ∫ s in Ioo (-a) a, ‖deriv W s‖ ^ 2) :=
    Submission.tdo_ods_integral_le_sqrt (fun s => ‖deriv W s‖) a ha hD2
  -- Step 7: combine.
  exact hmean.trans (add_le_add hW_cs hD_cs)

namespace Submission

/-- **One-dimensional sup bound** (used for `n = 1 < p < 2` in the proof of the Tilt-excess Decay
Theorem, Simon Ch. 5, 4.5).  If `w : ℝ¹ → ℝ^ℓ` is `K`-Lipschitz on the closed ball `B̄_a(0)` with
`a > 0`, then for every `x ∈ B̄_a(0)`
`|w(x)| ≤ ((2a)⁻¹ ∫_{B_a(0)} |w|²)^{1/2} + (2a ∫_{B_a(0)} |Dw|²)^{1/2}`.

Proof: `ι(t) = t e₁` maps `[-a, a]` isometrically into `B̄_a(0)`, so `W = w ∘ ι` is `K`-Lipschitz on
`[-a, a]`, and `x = ι(x₁)` with `x₁ ∈ [-a, a]`.  The interval bound `tdo_ods_interval_sup_le` at
`t = x₁` is the claim once both ball integrals are written as integrals over `(-a, a)`
(`tdo_ods_ball_integral_eq_interval`) and `|Dw(ι t)|² = |W'(t)|²`
(`tdo_ods_hsNormSq_fderiv_single`). -/
theorem tdo_one_dim_sup_le : ∀ (ℓ : ℕ) (w : Rn 1 → Rn ℓ) (a : ℝ) (K : ℝ≥0), 0 < a → LipschitzOnWith K w (closedBall 0 a) → ∀ x ∈ closedBall (0 : Rn 1) a, ‖w x‖ ≤ Real.sqrt ((2 * a)⁻¹ * ∫ y in ball (0 : Rn 1) a, ‖w y‖ ^ 2) + Real.sqrt (2 * a * ∫ y in ball (0 : Rn 1) a, hsNormSq (fderiv ℝ w y)) := by
  intro ℓ w a K ha hw x hx
  -- Step 2: the curve `W(t) = w(t e₁)` is `K`-Lipschitz on `[-a, a]`.
  set W : ℝ → Rn ℓ := fun s => w (EuclideanSpace.single (0 : Fin 1) s)
  have hmaps : ∀ s ∈ Icc (-a) a,
      EuclideanSpace.single (0 : Fin 1) s ∈ closedBall (0 : Rn 1) a := by
    intro s hs
    rw [mem_closedBall_zero_iff, PiLp.norm_single, Real.norm_eq_abs]
    exact abs_le.mpr hs
  have hWlip : LipschitzOnWith K W (Icc (-a) a) := by
    intro s hs t ht
    simpa only [W, PiLp.edist_single_same] using hw (hmaps s hs) (hmaps t ht)
  -- `x = x₁ e₁` with `x₁ ∈ [-a, a]`.
  have hx_eq : EuclideanSpace.single (0 : Fin 1) (x 0) = x := by
    ext i
    rw [Subsingleton.elim i 0, PiLp.single_eq_same]
  have hx0 : x 0 ∈ Icc (-a) a := by
    have h := mem_closedBall_zero_iff.mp hx
    rw [← hx_eq, PiLp.norm_single, Real.norm_eq_abs] at h
    exact abs_le.mp h
  -- Step 8: both ball integrals are integrals over `(-a, a)` along `W`.
  have h1 : (∫ y in ball (0 : Rn 1) a, ‖w y‖ ^ 2) = ∫ s in Ioo (-a) a, ‖W s‖ ^ 2 :=
    Submission.tdo_ods_ball_integral_eq_interval (fun y => ‖w y‖ ^ 2) a
  have h2 : (∫ y in ball (0 : Rn 1) a, hsNormSq (fderiv ℝ w y)) =
      ∫ s in Ioo (-a) a, ‖deriv W s‖ ^ 2 := by
    rw [Submission.tdo_ods_ball_integral_eq_interval (fun y => hsNormSq (fderiv ℝ w y)) a]
    exact integral_congr_ae (ae_of_all _ fun s =>
      Submission.tdo_ods_hsNormSq_fderiv_single ℓ w s)
  -- Steps 2–7: the interval bound for `W` at `t = x₁`.
  have hWx : W (x 0) = w x := congrArg w hx_eq
  rw [h1, h2, ← hWx]
  exact Submission.tdo_ods_interval_sup_le ℓ W a K ha hWlip (x 0) hx0
/-- **Distance to a nearby plane** (Simon Ch. 5, proof of 4.5): for subspaces `P`, `Q` of
`ℝ^{n+ℓ}` and `x ∈ ℝ^{n+ℓ}`, `dist(x, P) ≤ dist(x, Q) + |p_P − p_Q| |x|`.  The orthogonal
projections are nearest points, `x − p_P x = (x − p_Q x) − (p_P − p_Q) x`, and
`|(p_P − p_Q) x| ≤ |p_P − p_Q| |x|` by taking square roots in `lgc_hsNormSq_bounds`. -/
theorem tdo_stp_infDist_le_infDist_add_hsNorm : ∀ (n ℓ : ℕ) (P Q : Submodule ℝ (Amb n ℓ)) (x : Amb n ℓ), infDist x (P : Set (Amb n ℓ)) ≤ infDist x (Q : Set (Amb n ℓ)) + hsNorm (P.starProjection - Q.starProjection) * ‖x‖ := by
  intro n ℓ P Q x
  set A := P.starProjection - Q.starProjection with hA
  have hb := (lgc_hsNormSq_bounds (n + ℓ) (n + ℓ)).2 A
  -- `|A x| ≤ |A| |x|`: square roots of `|A x|² ≤ |A|² |x|²`.
  have hAx : ‖A x‖ ≤ hsNorm A * ‖x‖ := by
    unfold hsNorm
    rw [← Real.sqrt_sq (norm_nonneg (A x)), ← Real.sqrt_sq (norm_nonneg x),
      ← Real.sqrt_mul hb.1]
    exact Real.sqrt_le_sqrt (hb.2.2 x)
  -- The orthogonal projections are nearest points.
  rw [← P.dist_starProjection_eq_infDist x, ← Q.dist_starProjection_eq_infDist x,
    dist_eq_norm, dist_eq_norm]
  have hx : x - P.starProjection x = (x - Q.starProjection x) - A x := by
    rw [hA, sub_apply]
    abel
  calc ‖x - P.starProjection x‖ ≤ ‖x - Q.starProjection x‖ + ‖A x‖ := by
        rw [hx]
        exact norm_sub_le _ _
    _ ≤ ‖x - Q.starProjection x‖ + hsNorm A * ‖x‖ := by gcongr
/-- **Comparison of two planes by their tilt-excess** (proof of Simon Ch. 5, Theorem 4.5, p. 117:
`E(0, ρ, T)` and `E(0, ρ, T̃)` small give `|p_T − p_T̃|` small).  If `x ↦ p_{T_x M}` is
`μ_V`-a.e. strongly measurable and `μ_V(B_s(z)) < ∞`, then for all subspaces `P, Q`
`μ_V(B_s(z)) |p_P − p_Q|² ≤ 2 sⁿ (E(z, s, P) + E(z, s, Q))`: column by column,
`|a − b|² ≤ 2|a|² + 2|b|²` gives `|p_P − p_Q|² ≤ 2|p_{T_x M} − p_P|² + 2|p_{T_x M} − p_Q|²`
for every `x`, and integrating over `B_s(z)` gives the claim (the integrands are bounded since
all projections have operator norm `≤ 1`). -/
theorem tdo_stp_hsNormSq_sub_le_tiltExcess : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (z : Amb n ℓ) (s : ℝ), 0 < s → V.weight (closedBall z s) ≠ ⊤ → ∀ P Q : Submodule ℝ (Amb n ℓ), (V.weight (closedBall z s)).toReal * hsNormSq (P.starProjection - Q.starProjection) ≤ 2 * s ^ n * (V.tiltExcess z s P + V.tiltExcess z s Q) := by
  intro n ℓ U V hmeas z s hs hfin P Q
  obtain ⟨hcont, hbd⟩ := lgc_hsNormSq_bounds (n + ℓ) (n + ℓ)
  -- Tangent projections are orthogonal projections or `0`, so of operator norm `≤ 1`.
  have hproj : ∀ x, ‖V.tangentProj x‖ ≤ 1 := by
    intro x
    unfold RectifiableVarifold.tangentProj
    split_ifs
    · exact Submodule.starProjection_norm_le _
    · simp
  -- `x ↦ |p_{T_x M} − p_R|²` is a.e. strongly measurable and bounded by `4(n+ℓ)`, hence
  -- integrable on the ball of finite measure.
  have hint : ∀ R : Submodule ℝ (Amb n ℓ), IntegrableOn
      (fun x => hsNormSq (V.tangentProj x - R.starProjection)) (closedBall z s) V.weight := by
    intro R
    refine Measure.integrableOn_of_bounded (M := ((n + ℓ : ℕ) : ℝ) * 2 ^ 2) hfin
      (hcont.comp_aestronglyMeasurable (hmeas.sub aestronglyMeasurable_const))
      (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨h0, h1, -⟩ := hbd (V.tangentProj x - R.starProjection)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    refine h1.trans ?_
    gcongr
    calc ‖V.tangentProj x - R.starProjection‖
        ≤ ‖V.tangentProj x‖ + ‖R.starProjection‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hproj x) R.starProjection_norm_le
      _ = 2 := by norm_num
  -- Pointwise `|p_P − p_Q|² ≤ 2|p_{T_x M} − p_P|² + 2|p_{T_x M} − p_Q|²`, column by column.
  have hpt : ∀ x, hsNormSq (P.starProjection - Q.starProjection) ≤
      2 * hsNormSq (V.tangentProj x - P.starProjection) +
        2 * hsNormSq (V.tangentProj x - Q.starProjection) := by
    intro x
    unfold hsNormSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [sub_apply]
    set a := V.tangentProj x (EuclideanSpace.single i 1) - Q.starProjection (EuclideanSpace.single i 1)
    set b := V.tangentProj x (EuclideanSpace.single i 1) - P.starProjection (EuclideanSpace.single i 1)
    have hab : P.starProjection (EuclideanSpace.single i 1) - Q.starProjection (EuclideanSpace.single i 1)
        = a - b := by
      simp only [a, b]
      abel
    rw [hab]
    nlinarith [norm_sub_le a b, sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b,
      norm_nonneg (a - b)]
  -- Integrate the pointwise inequality over the ball.
  have hP := (hint P).const_mul 2
  have hQ := (hint Q).const_mul 2
  have key := setIntegral_ge_of_const_le_real measurableSet_closedBall hfin
    (fun x _ => hpt x) (hP.add hQ)
  rw [integral_add hP hQ, integral_const_mul, integral_const_mul, measureReal_def] at key
  -- `sⁿ E(z, s, R) = ∫_{B_s(z)} |p_{T_x M} − p_R|² dμ_V` since `s > 0`.
  unfold RectifiableVarifold.tiltExcess
  have hsn : s ^ n ≠ 0 := pow_ne_zero _ hs.ne'
  have hrw : 2 * s ^ n * ((s ^ n)⁻¹ *
        ∫ x in closedBall z s, hsNormSq (V.tangentProj x - P.starProjection) ∂V.weight +
      (s ^ n)⁻¹ *
        ∫ x in closedBall z s, hsNormSq (V.tangentProj x - Q.starProjection) ∂V.weight) =
      2 * ∫ x in closedBall z s, hsNormSq (V.tangentProj x - P.starProjection) ∂V.weight +
        2 * ∫ x in closedBall z s, hsNormSq (V.tangentProj x - Q.starProjection) ∂V.weight := by
    field_simp
  rw [hrw]
  linarith [key]
/-- **Simon Ch. 5, proof of Theorem 4.5, steps (1)–(2): the plane `T(0, 2δρ)`.**  Assume the Affine
Approximation Lemma 2.5, with constant `C_A = C_A(n, ℓ, p)`.  If 2.3 holds with `δ ∈ (0, 1/4]` and
`(σ^{p−n} ∫_{B_σ(0)} |H|ᵖ dμ_V)^{1/p} ≤ δ` for `σ = 2δρ`, then the plane `T` given by 2.5 at
`ξ = 0 ∈ spt V` and radius `2δρ` satisfies `E(0, δρ, T) ≤ C (δ^{1/(2n+2)})²` and
`dist(x, T) ≤ C δ^{1/(2n+2)} δρ` for `x ∈ spt V ∩ B_{2δρ}(0)`, with `C = 2ⁿ C_A² (C_A + 1)² + 2 C_A`.
Indeed `δ ≤ δ^{1/(2n+2)}`, so the right side of the first inequality of 2.5 is
`≤ (C_A + 1) δ^{1/(2n+2)}`, and `E(0, δρ, T) = 2ⁿ (2δρ)⁻ⁿ ∫_{B_{δρ}(0)} |p_{T_x M} − p_T|² dμ_V`;
each `dist(x, T)` is a term of the height supremum, so the second inequality of 2.5 gives
`dist(x, T) ≤ 2 C_A δ^{1/(2n+2)} δρ`. -/
theorem tdo_stp_origin_affine_plane : AffineApproximationLemma → ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 4 → V.AllardHypotheses H p δ ρ → V.scaledLpNorm H p 0 (2 * (δ * ρ)) ≤ ENNReal.ofReal δ → ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ V.tiltExcess 0 (δ * ρ) T ≤ C * (δ ^ (1 / (2 * (n : ℝ) + 2))) ^ 2 ∧ ∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)), infDist x (T : Set (Amb n ℓ)) ≤ C * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ) := by
  intro hAff n ℓ hn p hp
  -- The constant `C_A` of the Affine Approximation Lemma 2.5 for `(n, ℓ, p)`.
  obtain ⟨CA, hCA, hA⟩ := hAff n ℓ hn p hp
  refine ⟨2 ^ n * CA ^ 2 * (CA + 1) ^ 2 + 2 * CA, by positivity, ?_⟩
  intro U hU V H δ ρ hδ hδ4 hAH hK
  have hρ : 0 < ρ := hAH.1
  have h0 : (0 : Amb n ℓ) ∈ V.support := hAH.2.2.2.1
  have hσ : 0 < δ * ρ := mul_pos hδ hρ
  -- Lemma 2.5 at `ξ = 0` with radius `2δρ`.
  obtain ⟨T, hT, h2a, h2b⟩ := hA U hU V H δ ρ hδ hδ4 hAH 0 ⟨h0, mem_closedBall_self hσ.le⟩
    (2 * (δ * ρ)) (by positivity) (le_of_eq (by ring))
  set σ := δ * ρ
  set g := δ ^ (1 / (2 * (n : ℝ) + 2))
  have hg0 : 0 ≤ g := Real.rpow_nonneg hδ.le _
  -- `δ = δ ^ 1 ≤ δ ^ (1 / (2n + 2))` since `δ ≤ 1` and `1 / (2n + 2) ≤ 1`.
  have hδg : δ ≤ g := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hexp : 1 / (2 * (n : ℝ) + 2) ≤ 1 := by
      rw [div_le_one₀ (by positivity)]
      linarith
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ g := Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) hexp
  refine ⟨T, hT, ?_, ?_⟩
  · -- Tilt bound.
    rw [show 2 * σ / 2 = σ by ring] at h2a
    set J := ∫ x in closedBall (0 : Amb n ℓ) σ,
      hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight
    have hrhs : ENNReal.ofReal (2 * σ)⁻¹ * V.heightSup 0 (2 * σ) T +
        V.scaledLpNorm H p 0 (2 * σ) ≤ ENNReal.ofReal ((CA + 1) * g) := by
      calc _ ≤ ENNReal.ofReal (CA * g) + ENNReal.ofReal g :=
            add_le_add h2b (hK.trans (ENNReal.ofReal_le_ofReal hδg))
        _ = ENNReal.ofReal (CA * g + g) := (ENNReal.ofReal_add (by positivity) hg0).symm
        _ = ENNReal.ofReal ((CA + 1) * g) := by congr 1; ring
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h2a.trans hrhs)
    rw [inv_mul_le_iff₀ hCA] at h3
    have h4 : ((2 * σ) ^ n)⁻¹ * J ≤ (CA * ((CA + 1) * g)) ^ 2 :=
      (Real.sqrt_le_left (by positivity)).1 h3
    -- `σ⁻ⁿ J = 2ⁿ (2σ)⁻ⁿ J`.
    have h5 : V.tiltExcess 0 σ T = 2 ^ n * (((2 * σ) ^ n)⁻¹ * J) := by
      have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
      have key : ∀ s j : ℝ, (s ^ n)⁻¹ * j = 2 ^ n * (((2 * s) ^ n)⁻¹ * j) := fun s j => by
        rw [mul_pow, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ h2n, one_mul]
      exact key σ J
    rw [h5]
    calc 2 ^ n * (((2 * σ) ^ n)⁻¹ * J) ≤ 2 ^ n * (CA * ((CA + 1) * g)) ^ 2 := by gcongr
      _ = 2 ^ n * CA ^ 2 * (CA + 1) ^ 2 * g ^ 2 := by ring
      _ ≤ 2 ^ n * CA ^ 2 * (CA + 1) ^ 2 * g ^ 2 + 2 * CA * g ^ 2 :=
          le_add_of_nonneg_right (by positivity)
      _ = (2 ^ n * CA ^ 2 * (CA + 1) ^ 2 + 2 * CA) * g ^ 2 := by ring
  · -- Height bound.
    intro x hx
    have hle : ENNReal.ofReal (infDist x (T : Set (Amb n ℓ))) ≤ V.heightSup 0 (2 * σ) T :=
      calc ENNReal.ofReal (infDist x (T : Set (Amb n ℓ)))
          = ENNReal.ofReal (infDist (x - 0) (T : Set (Amb n ℓ))) := by rw [sub_zero]
        _ ≤ V.heightSup 0 (2 * σ) T :=
          le_iSup₂ (f := fun y (_ : y ∈ V.support ∩ closedBall (0 : Amb n ℓ) (2 * σ)) =>
            ENNReal.ofReal (infDist (y - 0) (T : Set (Amb n ℓ)))) x hx
    have h1 : ENNReal.ofReal (2 * σ)⁻¹ * ENNReal.ofReal (infDist x (T : Set (Amb n ℓ))) ≤
        ENNReal.ofReal (CA * g) :=
      le_trans (by gcongr) h2b
    rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity),
      inv_mul_le_iff₀ (by positivity)] at h1
    calc infDist x (T : Set (Amb n ℓ)) ≤ 2 * σ * (CA * g) := h1
      _ = 2 * CA * g * σ := by ring
      _ ≤ (2 ^ n * CA ^ 2 * (CA + 1) ^ 2 + 2 * CA) * g * σ := by
          gcongr
          exact le_add_of_nonneg_left (by positivity)
/-- Hölder's inequality on a set `B` for an arbitrary (not necessarily measurable) function
`g : X → [0, ∞]` and exponents `0 < q ≤ p`:
`∫⁻_B g^q dμ ≤ (∫⁻_B g^p dμ)^{q/p} μ(B)^{1-q/p}`, as used for the scaled `Lᵖ` bounds of the mean
curvature in the tilt-excess decay (cf. Simon Ch. 5, Remark 2.2, p. 107).
Replace `g^q` by a measurable minorant `G` with the same integral over `B`
(`exists_measurable_le_lintegral_eq`), write `G = (G^{p/q})^{q/p} · 1^{1-q/p}`, apply the
two-exponent Hölder inequality `ENNReal.lintegral_mul_norm_pow_le` for `μ.restrict B`, and use
`G^{p/q} ≤ (g^q)^{p/q} = g^p` with the monotonicity of the lower integral. -/
theorem tdo_slb_setLIntegral_rpow_le_holder : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (B : Set X) (g : X → ℝ≥0∞) (p q : ℝ), 0 < q → q ≤ p → ∫⁻ x in B, g x ^ q ∂μ ≤ (∫⁻ x in B, g x ^ p ∂μ) ^ (q / p) * μ B ^ (1 - q / p) := by
  intro X _ μ B g p q hq hqp
  -- 1. the exponents: `q / p, 1 - q / p ≥ 0` sum to `1`, and `(p / q) (q / p) = 1`, `q (p / q) = p`
  have hp : 0 < p := hq.trans_le hqp
  have ha : 0 ≤ q / p := (div_pos hq hp).le
  have hb : 0 ≤ 1 - q / p := sub_nonneg.mpr ((div_le_one hp).mpr hqp)
  have hab : q / p + (1 - q / p) = 1 := add_sub_cancel _ _
  have hpq : p / q * (q / p) = 1 := by field_simp
  have hqp' : q * (p / q) = p := by field_simp
  -- 2. a measurable minorant `G ≤ g ^ q` with the same integral over `B`
  obtain ⟨G, hGm, hGg, hG⟩ := exists_measurable_le_lintegral_eq (μ.restrict B) fun x => g x ^ q
  -- 3. `G = (G ^ (p / q)) ^ (q / p) * 1 ^ (1 - q / p)` pointwise
  have hGF : ∀ x, (G x ^ (p / q)) ^ (q / p) * (1 : ℝ≥0∞) ^ (1 - q / p) = G x := fun x => by
    rw [ENNReal.one_rpow, mul_one, ← ENNReal.rpow_mul, hpq, ENNReal.rpow_one]
  -- 4. Hölder for `G ^ (p / q)` and `1` with the exponents `q / p` and `1 - q / p` on `μ.restrict B`
  have hH := ENNReal.lintegral_mul_norm_pow_le (μ := μ.restrict B)
    (hGm.pow_const (p / q)).aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞))) ha hb hab
  -- 5. `G ^ (p / q) ≤ (g ^ q) ^ (p / q) = g ^ p`
  have hGp : ∀ x, G x ^ (p / q) ≤ g x ^ p := fun x => by
    calc G x ^ (p / q) ≤ (g x ^ q) ^ (p / q) := ENNReal.rpow_le_rpow (hGg x) (div_pos hp hq).le
      _ = g x ^ p := by rw [← ENNReal.rpow_mul, hqp']
  -- 6. chain the steps; `∫⁻_B 1 dμ = μ(B)`
  calc ∫⁻ x in B, g x ^ q ∂μ = ∫⁻ x in B, G x ∂μ := hG
    _ = ∫⁻ x in B, (G x ^ (p / q)) ^ (q / p) * (1 : ℝ≥0∞) ^ (1 - q / p) ∂μ := by
        simp only [hGF]
    _ ≤ (∫⁻ x in B, G x ^ (p / q) ∂μ) ^ (q / p) * (∫⁻ _ in B, (1 : ℝ≥0∞) ∂μ) ^ (1 - q / p) := hH
    _ = (∫⁻ x in B, G x ^ (p / q) ∂μ) ^ (q / p) * μ B ^ (1 - q / p) := by
        rw [setLIntegral_one]
    _ ≤ (∫⁻ x in B, g x ^ p ∂μ) ^ (q / p) * μ B ^ (1 - q / p) := by
        gcongr
        exact hGp _
/-- Scaling of the scaled `Lᵖ` norm of `H` on nested closed balls (Simon Ch. 5, end of the proof of
4.5, p. 121, where `B_{θσ}(0) ⊆ B_σ(0)` gives
`((θσ)^{p−n} ∫_{B_{θσ}(0)} |H|ᵖ dμ_V)^{1/p} ≤ θ^{1−n/p} (σ^{p−n} ∫_{B_σ(0)} |H|ᵖ dμ_V)^{1/p}`):
if `p > 0`, `0 < s ≤ t` and `B_s(z) ⊆ B_t(w)`, then
`(s^{p−n} ∫_{B_s(z)} |H|ᵖ dμ_V)^{1/p} ≤ (s/t)^{(p−n)/p} (t^{p−n} ∫_{B_t(w)} |H|ᵖ dμ_V)^{1/p}`.
The integral over the smaller ball is at most the one over the larger ball, the weight splits as
`s^{p−n} = (s/t)^{p−n} t^{p−n}`, and `x ↦ x^{1/p}` is monotone and multiplicative on `[0, ∞]`. -/
theorem tdo_slb_scaledLpNorm_le_of_subset : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (z w : Amb n ℓ) (s t : ℝ), 0 < p → 0 < s → s ≤ t → closedBall z s ⊆ closedBall w t → V.scaledLpNorm H p z s ≤ ENNReal.ofReal ((s / t) ^ ((p - n) / p)) * V.scaledLpNorm H p w t := by
  intro n ℓ U V H p z w s t hp hs hst hsub
  -- Step 1: `t > 0` and `s / t > 0`
  have ht : 0 < t := hs.trans_le hst
  have hst' : 0 ≤ s / t := (div_pos hs ht).le
  -- Step 2: monotonicity of the lower integral in the domain (no measurability needed)
  have hI : ∫⁻ x in closedBall z s, ‖H x‖ₑ ^ p ∂V.weight
      ≤ ∫⁻ x in closedBall w t, ‖H x‖ₑ ^ p ∂V.weight :=
    lintegral_mono_set hsub
  -- Step 3: `ofReal (s^{p−n}) = ofReal ((s/t)^{p−n}) * ofReal (t^{p−n})`
  have hsplit : ENNReal.ofReal (s ^ (p - n))
      = ENNReal.ofReal ((s / t) ^ (p - n)) * ENNReal.ofReal (t ^ (p - n)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hst' _), Real.div_rpow hs.le ht.le,
      div_mul_cancel₀ _ (Real.rpow_pos_of_pos ht _).ne']
  have hp' : 0 ≤ 1 / p := (one_div_pos.mpr hp).le
  unfold RectifiableVarifold.scaledLpNorm
  -- Steps 4–6: compare inside, take `1/p`-th powers, and simplify the coefficient
  calc (ENNReal.ofReal (s ^ (p - n)) * ∫⁻ x in closedBall z s, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)
      ≤ (ENNReal.ofReal ((s / t) ^ (p - n)) * (ENNReal.ofReal (t ^ (p - n))
          * ∫⁻ x in closedBall w t, ‖H x‖ₑ ^ p ∂V.weight)) ^ (1 / p) := by
        refine ENNReal.rpow_le_rpow ?_ hp'
        rw [hsplit, mul_assoc]
        gcongr
    _ = ENNReal.ofReal ((s / t) ^ (p - n)) ^ (1 / p) * (ENNReal.ofReal (t ^ (p - n))
          * ∫⁻ x in closedBall w t, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ hp'
    _ = ENNReal.ofReal ((s / t) ^ ((p - n) / p)) * (ENNReal.ofReal (t ^ (p - n))
          * ∫⁻ x in closedBall w t, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hst' _) hp', ← Real.rpow_mul hst',
          mul_one_div]
/-- Simon Ch. 5, Remark 2.2 (p. 107): the Hölder estimate of `∫_{B_s(z)} |H|^q dμ_V` by the scaled
`Lᵖ` norm on a larger ball `B_t(w) ⊇ B_s(z)`.  If `0 < q ≤ p` and `μ_V(B_s(z)) ≤ m`, then
`∫_{B_s(z)} |H|^q dμ_V ≤ m^{1−q/p} t^{q(n−p)/p} (t^{p−n} ∫_{B_t(w)} |H|ᵖ dμ_V)^{q/p}`
(lower integrals in `[0, ∞]`; no measurability of `H` and no condition on `s`). -/
theorem tdo_slb_lintegral_rpow_le_scaledLpNorm : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p q : ℝ) (z w : Amb n ℓ) (s t m : ℝ), 0 < q → q ≤ p → 0 < t → 0 ≤ m → closedBall z s ⊆ closedBall w t → V.weight (closedBall z s) ≤ ENNReal.ofReal m → ∫⁻ x in closedBall z s, ‖H x‖ₑ ^ q ∂V.weight ≤ ENNReal.ofReal (m ^ (1 - q / p) * t ^ (q * (n - p) / p)) * V.scaledLpNorm H p w t ^ q := by
  intro n ℓ U V H p q z w s t m hq hqp ht hm hsub hmass
  -- Step 1: `p > 0`, `a = q/p ≥ 0`, `b = 1 - q/p ≥ 0`.
  have hp : 0 < p := hq.trans_le hqp
  have ha : 0 ≤ q / p := (div_pos hq hp).le
  have hb : 0 ≤ 1 - q / p := sub_nonneg.2 ((div_le_one hp).2 hqp)
  -- Step 5: `I^a = ofReal(t^{q(n-p)/p}) · K(w, t)^q` with `I = ∫⁻_{B_t(w)} |H|ᵖ`.
  have hkey : ENNReal.ofReal (t ^ (q * (n - p) / p)) * V.scaledLpNorm H p w t ^ q =
      (∫⁻ x in closedBall w t, ‖H x‖ₑ ^ p ∂V.weight) ^ (q / p) := by
    have hexp : q * (n - p) / p + (p - n) * (q / p) = 0 := by
      field_simp
      ring
    rw [RectifiableVarifold.scaledLpNorm, ← ENNReal.rpow_mul, one_div_mul_eq_div,
      ENNReal.mul_rpow_of_nonneg _ _ ha,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.le _) ha, ← Real.rpow_mul ht.le,
      ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht, hexp,
      Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  calc ∫⁻ x in closedBall z s, ‖H x‖ₑ ^ q ∂V.weight
      ≤ (∫⁻ x in closedBall z s, ‖H x‖ₑ ^ p ∂V.weight) ^ (q / p) *
          V.weight (closedBall z s) ^ (1 - q / p) :=
        Submission.tdo_slb_setLIntegral_rpow_le_holder (Amb n ℓ) V.weight (closedBall z s)
          (fun x => ‖H x‖ₑ) p q hq hqp
    -- Step 3: enlarge the domain to `B_t(w)` and bound the mass by `m`.
    _ ≤ (∫⁻ x in closedBall w t, ‖H x‖ₑ ^ p ∂V.weight) ^ (q / p) *
          ENNReal.ofReal m ^ (1 - q / p) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (lintegral_mono_set hsub) ha)
          (ENNReal.rpow_le_rpow hmass hb)
    -- Steps 4 and 6: recombine the constants.
    _ = ENNReal.ofReal (m ^ (1 - q / p) * t ^ (q * (n - p) / p)) * V.scaledLpNorm H p w t ^ q := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hm _), mul_assoc, hkey,
          ← ENNReal.ofReal_rpow_of_nonneg hm hb, mul_comm]
/-- **Scaling and Hölder bounds for the scaled `Lᵖ` norm** (used in the proof of Simon Ch. 5,
Theorem 4.5, pp. 117–121; part (b) generalizes the Hölder step of Remark 2.2, p. 107).  Write
`K(y, r) = (r^{p−n} ∫_{B_r(y)} |H|ᵖ dμ_V)^{1/p} ∈ [0, ∞]` (`V.scaledLpNorm`, closed balls, lower
integrals, `H` arbitrary).
(a) If `p > 0`, `0 < s ≤ t` and `B_s(z) ⊆ B_t(w)`, then `K(z, s) ≤ (s/t)^{(p−n)/p} K(w, t)`.
(b) If `0 < q ≤ p`, `t > 0`, `m ≥ 0`, `B_s(z) ⊆ B_t(w)` and `μ_V(B_s(z)) ≤ m`, then
`∫_{B_s(z)} |H|^q dμ_V ≤ m^{1−q/p} t^{q(n−p)/p} K(w, t)^q`.

Part (a) is `tdo_slb_scaledLpNorm_le_of_subset`: monotonicity of the `p`-integral in the ball and
`s^{p−n} = (s/t)^{p−n} t^{p−n}`, followed by taking `1/p`-th powers.  Part (b) is
`tdo_slb_lintegral_rpow_le_scaledLpNorm`: Hölder's inequality on `B_s(z)` for the possibly
non-measurable `|H|` (`tdo_slb_setLIntegral_rpow_le_holder`), the bounds
`∫_{B_s(z)} |H|ᵖ ≤ ∫_{B_t(w)} |H|ᵖ` and `μ_V(B_s(z)) ≤ m`, and the identity
`(∫_{B_t(w)} |H|ᵖ dμ_V)^{q/p} = t^{q(n−p)/p} K(w, t)^q`. -/
theorem tdo_scaledLpNorm_bounds : (∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (z w : Amb n ℓ) (s t : ℝ), 0 < p → 0 < s → s ≤ t → closedBall z s ⊆ closedBall w t → V.scaledLpNorm H p z s ≤ ENNReal.ofReal ((s / t) ^ ((p - n) / p)) * V.scaledLpNorm H p w t) ∧ (∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p q : ℝ) (z w : Amb n ℓ) (s t m : ℝ), 0 < q → q ≤ p → 0 < t → 0 ≤ m → closedBall z s ⊆ closedBall w t → V.weight (closedBall z s) ≤ ENNReal.ofReal m → ∫⁻ x in closedBall z s, ‖H x‖ₑ ^ q ∂V.weight ≤ ENNReal.ofReal (m ^ (1 - q / p) * t ^ (q * (n - p) / p)) * V.scaledLpNorm H p w t ^ q) :=
  ⟨Submission.tdo_slb_scaledLpNorm_le_of_subset, Submission.tdo_slb_lintegral_rpow_le_scaledLpNorm⟩
/-- **Simon Ch. 5, Remark 4.6 (p. 116)**: the trivial comparison of tilt-excesses on nested balls.
If `0 < s ≤ t` and `B_s(z) ⊆ B_t(w) ⊆ U` (closed balls), then for every subspace `S`
`E(z, s, S) ≤ (t/s)ⁿ E(w, t, S)`.  The integrand `φ(x) = |p_{T_x M} − p_S|²` satisfies
`0 ≤ φ ≤ 4(n + ℓ)`, since both projections have operator norm `≤ 1`, and it is `μ_V`-a.e. strongly
measurable because `A ↦ |A − p_S|²` is continuous.  As `B_t(w) ⊆ U` is compact,
`μ_V(B_t(w)) = ∫_{M ∩ B_t(w)} θ dHⁿ < ∞`, so `φ` is integrable on `B_t(w)` and
`∫_{B_s(z)} φ dμ_V ≤ ∫_{B_t(w)} φ dμ_V`; finally `s⁻ⁿ = (t/s)ⁿ t⁻ⁿ`. -/
theorem tdo_tiltExcess_le_of_subset : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (z w : Amb n ℓ) (s t : ℝ) (S : Submodule ℝ (Amb n ℓ)), 0 < s → s ≤ t → closedBall z s ⊆ closedBall w t → closedBall w t ⊆ U → V.tiltExcess z s S ≤ (t / s) ^ n * V.tiltExcess w t S := by
  intro n ℓ U V hmeas z w s t S hs hst hsub hU
  -- Notation: `φ(x) = |p_{T_x M} − p_S|²`.
  set φ : Amb n ℓ → ℝ := fun x => hsNormSq (V.tangentProj x - S.starProjection)
  -- Step 1: `0 ≤ φ ≤ 4(n + ℓ)`, as `‖p_{T_x M}‖ ≤ 1` (a projection, or `0`) and `‖p_S‖ ≤ 1`.
  have hnorm : ∀ x, ‖V.tangentProj x‖ ≤ 1 := by
    intro x
    unfold RectifiableVarifold.tangentProj
    split_ifs
    · exact Submodule.starProjection_norm_le _
    · simp
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hφle : ∀ x, ‖φ x‖ ≤ 4 * ((n + ℓ : ℕ) : ℝ) := by
    intro x
    rw [Real.norm_of_nonneg (hφ0 x)]
    have hA : ‖V.tangentProj x - S.starProjection‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [hnorm x, S.starProjection_norm_le])
    calc φ x ≤ ∑ _i : Fin (n + ℓ), (2 : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          calc _ ≤ ‖V.tangentProj x - S.starProjection‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
                (V.tangentProj x - S.starProjection).le_opNorm _
            _ ≤ 2 := by simpa using hA
      _ = 4 * ((n + ℓ : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- Step 2: `φ` is `μ_V`-a.e. strongly measurable, since `A ↦ |A − p_S|²` is continuous.
  have hcont : Continuous fun A : Amb n ℓ →L[ℝ] Amb n ℓ => hsNormSq (A - S.starProjection) := by
    unfold hsNormSq
    exact continuous_finsetSum _ fun i _ =>
      (((continuous_id.sub continuous_const).clm_apply continuous_const).norm).pow 2
  have hφmeas : AEStronglyMeasurable φ V.weight := hcont.comp_aestronglyMeasurable hmeas
  -- Step 3: `μ_V(B_t(w)) = ∫_{M ∩ B_t(w)} θ dHⁿ < ∞`, as `B_t(w) ⊆ U` is compact.
  have hK : IsCompact (closedBall w t) := isCompact_closedBall w t
  have hfin : V.weight (closedBall w t) < ⊤ := by
    rw [RectifiableVarifold.weight, withDensity_apply _ hK.isClosed.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm (closedBall w t) V.carrier]
    exact (V.integrableOn_mult _ hK hU).lintegral_lt_top
  -- Step 4: `φ` is integrable on `B_t(w)`, so `∫_{B_s(z)} φ dμ_V ≤ ∫_{B_t(w)} φ dμ_V`.
  have hint : IntegrableOn φ (closedBall w t) V.weight :=
    Measure.integrableOn_of_bounded hfin.ne hφmeas (Eventually.of_forall hφle)
  have hmono : ∫ x in closedBall z s, φ x ∂V.weight ≤ ∫ x in closedBall w t, φ x ∂V.weight :=
    setIntegral_mono_set hint (Eventually.of_forall hφ0) (Eventually.of_forall hsub)
  -- Step 5: `s⁻ⁿ = (t/s)ⁿ t⁻ⁿ`, as `0 < s ≤ t`.
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hscale : (s ^ n)⁻¹ = (t / s) ^ n * (t ^ n)⁻¹ := by
    rw [div_pow]
    field_simp
  unfold RectifiableVarifold.tiltExcess
  calc (s ^ n)⁻¹ * ∫ x in closedBall z s, φ x ∂V.weight
      ≤ (s ^ n)⁻¹ * ∫ x in closedBall w t, φ x ∂V.weight :=
        mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 (pow_nonneg hs.le n))
    _ = (t / s) ^ n * ((t ^ n)⁻¹ * ∫ x in closedBall w t, φ x ∂V.weight) := by
        rw [hscale, mul_assoc]
/-- **Reduction to a plane of small tilt and small height** (Simon Ch. 5, proof of Theorem 4.5,
steps (1), (2)).  Write `g = δ^{1/(2n+2)}`, `σ = δρ` and `K(y, r) = V.scaledLpNorm H p y r`.  The
scaling bound gives `K(0, 2σ) ≤ K(0, ρ) ≤ δ`, so affine approximation at the origin and scale `2σ`
yields a plane `T̃` with `E(0, σ, T̃) ≤ C₀ g²` and `dist(x, T̃) ≤ C₀ g σ` on `spt V ∩ B_{2σ}(0)`.
If `E(0, σ, T) > C₀ g²` we take `T' = T̃`, which does not increase `E_*`.  Otherwise `T' = T`:
integrating `|p_T − p_T̃|² ≤ 2|p_x − p_T|² + 2|p_x − p_T̃|²` against the lower mass bound
`μ_V(B_σ(0)) ≥ ω_n σⁿ/2` gives `|p_T − p_T̃| ≤ (8 C₀/ω_n)^{1/2} g`, and
`dist(x, T) ≤ dist(x, T̃) + |p_T − p_T̃| |x|` transfers the height bound to `T`. -/
theorem tdo_small_tilt_plane : AffineApproximationLemma → ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 4 → V.AllardHypotheses H p δ ρ → AEStronglyMeasurable V.tangentProj V.weight → ENNReal.ofReal (unitBallVolume n * (δ * ρ) ^ n / 2) ≤ V.weight (closedBall 0 (δ * ρ)) → ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → ∃ T' : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T' = n ∧ V.tiltExcessStar H p δ 0 (δ * ρ) T' ≤ V.tiltExcessStar H p δ 0 (δ * ρ) T ∧ V.tiltExcess 0 (δ * ρ) T' ≤ C * (δ ^ (1 / (2 * (n : ℝ) + 2))) ^ 2 ∧ ∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)), infDist x (T' : Set (Amb n ℓ)) ≤ C * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ) := by
  intro hAff n ℓ hn p hnp
  obtain ⟨C₀, hC₀, hA⟩ := tdo_stp_origin_affine_plane hAff n ℓ hn p hnp
  -- `ω_n = π^{n/2} / Γ(n/2 + 1) > 0`.
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  set C₁ : ℝ := Real.sqrt (8 * C₀ / unitBallVolume n) with hC₁
  have hC₁0 : 0 ≤ C₁ := Real.sqrt_nonneg _
  refine ⟨C₀ + 2 * C₁, by linarith, ?_⟩
  intro U hU V H δ ρ hδ hδ4 hAH hmeas hmass T hT
  have hρ : 0 < ρ := hAH.1
  have hσ : 0 < δ * ρ := mul_pos hδ hρ
  have h2σ : 2 * (δ * ρ) ≤ ρ := by
    have := mul_le_mul_of_nonneg_right hδ4 hρ.le
    linarith
  have hp : 0 < p := (Nat.cast_nonneg n).trans_lt hnp
  -- Step (1a): `K(0, 2δρ) ≤ (2δρ/ρ)^{(p-n)/p} K(0, ρ) ≤ K(0, ρ) ≤ δ`.
  have hK2σ : V.scaledLpNorm H p 0 (2 * (δ * ρ)) ≤ ENNReal.ofReal δ := by
    have hr : (2 * (δ * ρ) / ρ) ^ ((p - n) / p) ≤ 1 :=
      Real.rpow_le_one (div_nonneg (by linarith) hρ.le) ((div_le_one hρ).2 h2σ)
        (div_nonneg (sub_nonneg.2 hnp.le) hp.le)
    calc V.scaledLpNorm H p 0 (2 * (δ * ρ))
        ≤ ENNReal.ofReal ((2 * (δ * ρ) / ρ) ^ ((p - n) / p)) * V.scaledLpNorm H p 0 ρ :=
          tdo_scaledLpNorm_bounds.1 n ℓ U V H p 0 0 (2 * (δ * ρ)) ρ hp (by linarith) h2σ
            (closedBall_subset_closedBall h2σ)
      _ ≤ V.scaledLpNorm H p 0 ρ :=
          mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 hr)
      _ ≤ ENNReal.ofReal δ := hAH.2.2.2.2.2.2
  -- The plane `T̃` of affine approximation at the origin and scale `2δρ`.
  obtain ⟨T₁, hT₁, hE₁, hH₁⟩ := hA U hU V H δ ρ hδ hδ4 hAH hK2σ
  set g : ℝ := δ ^ (1 / (2 * (n : ℝ) + 2))
  have hg0 : 0 ≤ g := Real.rpow_nonneg hδ.le _
  by_cases hcase : C₀ * g ^ 2 < V.tiltExcess 0 (δ * ρ) T
  · -- Case A: replace `T` by `T̃`, which does not increase `E_*`.
    refine ⟨T₁, hT₁, ?_, hE₁.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg g)),
      fun x hx => (hH₁ x hx).trans ?_⟩
    · unfold RectifiableVarifold.tiltExcessStar
      exact max_le_max (hE₁.trans hcase.le) le_rfl
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hg0) hσ.le
  · -- Case B: keep `T` and transfer the height bound from `T̃` to `T`.
    have hET : V.tiltExcess 0 (δ * ρ) T ≤ C₀ * g ^ 2 := not_lt.1 hcase
    refine ⟨T, hT, le_rfl, hET.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg g)),
      fun x hx => ?_⟩
    -- `ω_n (δρ)ⁿ/2 ≤ μ_V(B_{δρ}(0)) ≤ μ_V(B_ρ(0)) < ∞`.
    have hfin : V.weight (closedBall 0 (δ * ρ)) ≠ ⊤ :=
      ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hAH.2.2.2.2.2.1)
        (measure_mono (closedBall_subset_closedBall (by linarith)))
    have hw : unitBallVolume n * (δ * ρ) ^ n / 2 ≤ (V.weight (closedBall 0 (δ * ρ))).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hfin).1 hmass
    have hD0 : 0 ≤ hsNormSq (T.starProjection - T₁.starProjection) := by
      unfold hsNormSq
      positivity
    -- `|p_T − p_T̃|² ≤ 8 C₀ g²/ω_n`.
    have hDsq : hsNormSq (T.starProjection - T₁.starProjection) ≤
        8 * C₀ / unitBallVolume n * g ^ 2 := by
      have h1 : unitBallVolume n * (δ * ρ) ^ n / 2 *
          hsNormSq (T.starProjection - T₁.starProjection) ≤
          2 * (δ * ρ) ^ n * (C₀ * g ^ 2 + C₀ * g ^ 2) :=
        calc _ ≤ (V.weight (closedBall 0 (δ * ρ))).toReal *
              hsNormSq (T.starProjection - T₁.starProjection) :=
              mul_le_mul_of_nonneg_right hw hD0
          _ ≤ 2 * (δ * ρ) ^ n * (V.tiltExcess 0 (δ * ρ) T + V.tiltExcess 0 (δ * ρ) T₁) :=
              tdo_stp_hsNormSq_sub_le_tiltExcess n ℓ U V hmeas 0 (δ * ρ) hσ hfin T T₁
          _ ≤ 2 * (δ * ρ) ^ n * (C₀ * g ^ 2 + C₀ * g ^ 2) :=
              mul_le_mul_of_nonneg_left (add_le_add hET hE₁)
                (mul_nonneg zero_le_two (pow_pos hσ n).le)
      have h2 : unitBallVolume n * hsNormSq (T.starProjection - T₁.starProjection) ≤
          8 * C₀ * g ^ 2 :=
        le_of_mul_le_mul_right (by linarith) (pow_pos hσ n)
      rw [div_mul_eq_mul_div, le_div_iff₀ hω]
      linarith
    have hDn : hsNorm (T.starProjection - T₁.starProjection) ≤ C₁ * g :=
      calc hsNorm (T.starProjection - T₁.starProjection)
          = Real.sqrt (hsNormSq (T.starProjection - T₁.starProjection)) := rfl
        _ ≤ Real.sqrt (8 * C₀ / unitBallVolume n * g ^ 2) := Real.sqrt_le_sqrt hDsq
        _ = C₁ * g := by rw [hC₁, Real.sqrt_mul' _ (sq_nonneg g), Real.sqrt_sq hg0]
    calc infDist x (T : Set (Amb n ℓ))
        ≤ infDist x (T₁ : Set (Amb n ℓ)) + hsNorm (T.starProjection - T₁.starProjection) * ‖x‖ :=
          tdo_stp_infDist_le_infDist_add_hsNorm n ℓ T T₁ x
      _ ≤ C₀ * g * (δ * ρ) + C₁ * g * (2 * (δ * ρ)) :=
          add_le_add (hH₁ x hx)
            (mul_le_mul hDn (mem_closedBall_zero_iff.1 hx.2) (norm_nonneg x) (mul_nonneg hC₁0 hg0))
      _ = (C₀ + 2 * C₁) * g * (δ * ρ) := by ring

/-- **Simon Ch. 5, proof of Theorem 4.5, the height bound before (20)** (pp. 119–120).  Let `q` be a
linear isometry of `ℝ^{n+ℓ}`, `f` `1`-Lipschitz on `B̄ⁿ_R(0)`, `λ(x') = c + A x'`,
`τ = q(0, c)`, `S = q{(v, A v)}` and `Γ = q(graph f|B̄ⁿ_R(0))`.  If `B̄_r(τ) ⊆ B̄_R(0)`,
`θ ≤ 2` `μ_V`-a.e. on `B̄_r(τ)`, `dist(x − τ, S) ≤ h` on `spt V ∩ B̄_r(τ)` and
`μ_V(B̄_R(0) ∩ (spt V \ Γ)) ≤ β`, then
`∫_{B̄_r(τ)} dist(x − τ, S)² dμ_V ≤ 2 · 2^{n/2} ∫_{Bⁿ_r(0)} |f − λ|² dLⁿ + h² β`.
Split `B̄_r(τ)` along the compact set `Γ` (compact as `x' ↦ q(x', f x')` is `√2`-Lipschitz,
`allard52_cft_graph_map_sqrt_two`).  On `Γ`, `θ ≤ 2` turns `μ_V` into `2 Hⁿ`
(`tdo_ghe_setLIntegral_weight_le_mul`), the area bound `tdo_graph_lintegral_le` with `L = 1` gives
the factor `√2ⁿ`, and at `x = q(x', f x') ∈ B̄_r(τ)` one has `|x'| ≤ r` and
`dist(x − τ, S) ≤ |f(x') − λ(x')|` (`tdo_graph_plane_dist` (iv), (iii)); the closed ball is then
traded for the open one (`tdo_ghe_lintegral_closedBall_ofReal_eq`).  Off `Γ`, `μ_V`-a.e. point
lies in `spt V` (`tdo_ghe_ae_mem_support`), where `dist(x − τ, S)² ≤ h²`, and these points have
weight at most `β`. -/
theorem tdo_graph_height_excess : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (c : Rn ℓ) (A : Rn n →L[ℝ] Rn ℓ) (R r h β : ℝ), 0 < r → r ≤ R → closedBall 0 R ⊆ U → LipschitzOnWith 1 f (closedBall (0 : Rn n) R) → closedBall (q (graphPoint (0 : Rn n) c)) r ⊆ closedBall 0 R → 0 ≤ β → (∀ᵐ x ∂V.weight, x ∈ closedBall (q (graphPoint (0 : Rn n) c)) r → V.mult x ≤ 2) → (∀ x ∈ V.support ∩ closedBall (q (graphPoint (0 : Rn n) c)) r, infDist (x - q (graphPoint (0 : Rn n) c)) (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) : Set (Amb n ℓ)) ≤ h) → V.weight (closedBall 0 R ∩ (V.support \ q '' graphOver f (closedBall 0 R))) ≤ ENNReal.ofReal β → ∫ x in closedBall (q (graphPoint (0 : Rn n) c)) r, infDist (x - q (graphPoint (0 : Rn n) c)) (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) : Set (Amb n ℓ)) ^ 2 ∂V.weight ≤ 2 * Real.sqrt 2 ^ n * (∫ x' in ball (0 : Rn n) r, ‖f x' - (c + A x')‖ ^ 2) + h ^ 2 * β := by
  intro n ℓ U V q f c A R r h β hr hrR _hRU hf hBR hβ hθ hh hweight
  set τ : Amb n ℓ := q (graphPoint (0 : Rn n) c)
  set S : Submodule ℝ (Amb n ℓ) :=
    Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v)))
  set B : Set (Amb n ℓ) := closedBall τ r
  set Γ : Set (Amb n ℓ) := q '' graphOver f (closedBall 0 R) with hΓ
  set X : ℝ := ∫ x' in ball (0 : Rn n) r, ‖f x' - (c + A x')‖ ^ 2
  -- `d(x) = dist(x − τ, S)` is continuous, so `ofReal (d²)` is measurable
  have hd : Continuous fun x : Amb n ℓ => infDist (x - τ) (S : Set (Amb n ℓ)) :=
    (continuous_infDist_pt _).comp (continuous_id.sub continuous_const)
  have hdm : Measurable fun x : Amb n ℓ =>
      ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2) :=
    ENNReal.measurable_ofReal.comp (hd.pow 2).measurable
  have hBm : MeasurableSet B := measurableSet_closedBall
  -- `Γ` is the image of the compact `B̄ⁿ_R(0)` under the `√2`-Lipschitz map `x' ↦ q(x', f x')`
  have hF : ContinuousOn (fun x' => q (graphPoint x' (f x'))) (closedBall (0 : Rn n) R) := by
    have h2 := (allard52_cft_graph_map_sqrt_two n ℓ q f (closedBall 0 R) hf).1
    refine (LipschitzOnWith.of_dist_le_mul (K := (Real.sqrt 2).toNNReal)
      fun x hx y hy => ?_).continuousOn
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    exact h2 x hx y hy
  have hΓm : MeasurableSet Γ := by
    have hΓF : Γ = (fun x' => q (graphPoint x' (f x'))) '' closedBall (0 : Rn n) R := by
      rw [hΓ, graphOver, Set.image_image]
    rw [hΓF]
    exact ((isCompact_closedBall _ _).image_of_continuousOn hF).isClosed.measurableSet
  have hX0 : 0 ≤ 2 * Real.sqrt 2 ^ n * X :=
    mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _)
  have hhβ : 0 ≤ h ^ 2 * β := mul_nonneg (sq_nonneg h) hβ
  -- at `x = q(x', f x') ∈ B̄_r(τ)`: `|x'| ≤ r` and `d(x) ≤ |f(x') − λ(x')|`
  have hpt : ∀ x' ∈ closedBall (0 : Rn n) R,
      B.indicator (fun x => ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2))
          (q (graphPoint x' (f x'))) ≤
        (closedBall (0 : Rn n) r).indicator
          (fun x' => ENNReal.ofReal (‖f x' - (c + A x')‖ ^ 2)) x' := by
    intro x' _
    obtain ⟨-, -, hdist, hnorm, -⟩ := tdo_graph_plane_dist n ℓ q A
    by_cases hx : q (graphPoint x' (f x')) ∈ B
    · have hx' : x' ∈ closedBall (0 : Rn n) r := by
        rw [mem_closedBall, dist_zero_right]
        exact (hnorm x' (f x') c).trans (by rw [← dist_eq_norm]; exact hx)
      rw [indicator_of_mem hx, indicator_of_mem hx']
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ infDist_nonneg (hdist x' (f x') c) 2)
    · rw [indicator_of_notMem hx]
      exact zero_le
  -- the part on `Γ`: `θ ≤ 2`, the area bound with `L = 1`, the pointwise bound, `B̄ⁿ_r ⊆ B̄ⁿ_R`
  have hφ : ContinuousOn (fun x' => ‖f x' - (c + A x')‖ ^ 2) (closedBall (0 : Rn n) r) :=
    (((hf.continuousOn.mono (closedBall_subset_closedBall hrR)).sub
      (continuousOn_const.add A.continuous.continuousOn)).norm).pow 2
  have hon : ∫⁻ x in B ∩ Γ, ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2) ∂V.weight ≤
      ENNReal.ofReal (2 * Real.sqrt 2 ^ n * X) := by
    calc ∫⁻ x in B ∩ Γ, ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2) ∂V.weight
        ≤ ENNReal.ofReal 2 * ∫⁻ x in B ∩ Γ, ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2)
            ∂(μHE[n] : Measure (Amb n ℓ)) :=
          Submission.tdo_ghe_setLIntegral_weight_le_mul n ℓ U V (B ∩ Γ) 2 _ (hBm.inter hΓm) hdm
            (hθ.mono fun x hx hxE => hx hxE.1)
      _ = ENNReal.ofReal 2 * ∫⁻ x in Γ, B.indicator
            (fun x => ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2)) x
            ∂(μHE[n] : Measure (Amb n ℓ)) := by
          rw [setLIntegral_indicator hBm]
      _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (Real.sqrt (1 + ((1 : ℝ≥0) : ℝ) ^ 2) ^ n) *
            ∫⁻ x' in closedBall (0 : Rn n) R, B.indicator
              (fun x => ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2))
              (q (graphPoint x' (f x')))) := by
          gcongr
          exact tdo_graph_lintegral_le n ℓ q f (closedBall 0 R) 1 measurableSet_closedBall hf _
            (hdm.indicator hBm)
      _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (Real.sqrt 2 ^ n) *
            ∫⁻ x' in closedBall (0 : Rn n) r, ENNReal.ofReal (‖f x' - (c + A x')‖ ^ 2)) := by
          have h12 : Real.sqrt (1 + ((1 : ℝ≥0) : ℝ) ^ 2) = Real.sqrt 2 := by norm_num
          rw [h12]
          gcongr ENNReal.ofReal 2 * (ENNReal.ofReal (Real.sqrt 2 ^ n) * ?_)
          calc ∫⁻ x' in closedBall (0 : Rn n) R, B.indicator
                (fun x => ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2))
                (q (graphPoint x' (f x')))
              ≤ ∫⁻ x' in closedBall (0 : Rn n) R, (closedBall (0 : Rn n) r).indicator
                (fun x' => ENNReal.ofReal (‖f x' - (c + A x')‖ ^ 2)) x' :=
                setLIntegral_mono' measurableSet_closedBall hpt
            _ ≤ ∫⁻ x', (closedBall (0 : Rn n) r).indicator
                (fun x' => ENNReal.ofReal (‖f x' - (c + A x')‖ ^ 2)) x' :=
                setLIntegral_le_lintegral _ _
            _ = ∫⁻ x' in closedBall (0 : Rn n) r, ENNReal.ofReal (‖f x' - (c + A x')‖ ^ 2) :=
                lintegral_indicator measurableSet_closedBall _
      _ = ENNReal.ofReal (2 * Real.sqrt 2 ^ n * X) := by
          rw [Submission.tdo_ghe_lintegral_closedBall_ofReal_eq n
              (fun x' => ‖f x' - (c + A x')‖ ^ 2) r hr hφ fun _ _ => sq_nonneg _,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num), mul_assoc]
  -- the part off `Γ`: `μ_V`-a.e. such point lies in `spt V ∩ B̄_r(τ)`, where `d ≤ h`
  have hae := Submission.tdo_ghe_ae_mem_support n ℓ U V
  have hoff : ∫⁻ x in B \ Γ, ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2) ∂V.weight ≤
      ENNReal.ofReal (h ^ 2 * β) := by
    calc ∫⁻ x in B \ Γ, ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2) ∂V.weight
        ≤ ∫⁻ _ in B \ Γ, ENNReal.ofReal (h ^ 2) ∂V.weight := by
          refine setLIntegral_mono_ae' (hBm.diff hΓm) ?_
          filter_upwards [hae] with x hxV hx
          exact ENNReal.ofReal_le_ofReal
            (pow_le_pow_left₀ infDist_nonneg (hh x ⟨hxV, hx.1⟩) 2)
      _ = ENNReal.ofReal (h ^ 2) * V.weight (B \ Γ) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (h ^ 2) * ENNReal.ofReal β := by
          gcongr
          refine (measure_mono_ae ?_).trans hweight
          filter_upwards [hae] with x hxV hx
          exact ⟨hBR hx.1, hxV, hx.2⟩
      _ = ENNReal.ofReal (h ^ 2 * β) := (ENNReal.ofReal_mul (sq_nonneg h)).symm
  -- add the two parts and return to the Bochner integral
  have htot : ∫⁻ x in B, ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2) ∂V.weight ≤
      ENNReal.ofReal (2 * Real.sqrt 2 ^ n * X + h ^ 2 * β) := by
    rw [← lintegral_inter_add_sdiff _ B hΓm, ENNReal.ofReal_add hX0 hhβ]
    exact add_le_add hon hoff
  have hint : ∫ x in B, infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2 ∂V.weight =
      (∫⁻ x in B, ENNReal.ofReal (infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2) ∂V.weight).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      (hd.pow 2).aestronglyMeasurable
  rw [hint]
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg hX0 hhβ) htot

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
