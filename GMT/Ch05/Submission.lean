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
import Poincare.SimonGMT.Chapter02.AreaLipschitz
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

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
/-- The weight `μ_V = Hⁿ ⌞ θ` of a rectifiable `n`-varifold `V = v(M, θ)` in `U` (steps 2(i), 2(ii)
and 8 of the proof of Simon Ch. 5, Theorem 4.5, pp. 118–119): `μ_V(K) < ∞` for compact `K ⊆ U`,
`μ_V` vanishes off `spt V`, and `μ_V ≪ Hⁿ` (every `Hⁿ`-null set, measurable or not, is
`μ_V`-null). -/
theorem gte_weight_null_finite : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), (∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U → V.weight K < ⊤) ∧ V.weight (V.support)ᶜ = 0 ∧ ∀ Z : Set (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) Z = 0 → V.weight Z = 0 := by
  intro n ℓ U V
  -- `μ_V = (Hⁿ ⌞ M).withDensity (ofReal ∘ θ) ≪ Hⁿ ⌞ M ≪ Hⁿ`
  have hM : V.weight ≪ (μHE[n] : Measure (Amb n ℓ)).restrict V.carrier :=
    withDensity_absolutelyContinuous _ _
  have hH : V.weight ≪ (μHE[n] : Measure (Amb n ℓ)) :=
    hM.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  refine ⟨fun K hK hKU => ?_, ?_, fun Z hZ => hH hZ⟩
  -- (i): `μ_V(K) = ∫⁻_{M ∩ K} ofReal θ dHⁿ ≤ ∫⁻_{M ∩ K} ‖θ‖ₑ dHⁿ < ∞`, `θ` integrable on `M ∩ K`
  · rw [RectifiableVarifold.weight, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (lintegral_mono fun x => Real.ofReal_le_enorm (V.mult x)).trans_lt
      (V.integrableOn_mult K hK hKU).hasFiniteIntegral
  -- (ii): `(spt V)ᶜ = Uᶜ ∪ (spt μ_V)ᶜ`; `μ_V` is conull on its support, and `Hⁿ ⌞ M` vanishes
  -- on `Uᶜ` because `M ⊆ U`
  · rw [RectifiableVarifold.support, compl_inter]
    refine measure_union_null (hM ?_) Measure.measure_compl_support
    rw [Measure.restrict_apply₀' V.nullMeasurableSet_carrier]
    exact measure_mono_null (fun x hx => hx.1 (V.carrier_subset hx.2)) measure_empty
/-- Tangent projections and the integrands of the graph tangential estimate (steps 1(iii) and 3 of
its proof, for Simon Ch. 5, Theorem 4.5, displays (8)–(12)): `p_x = V.tangentProj x` satisfies
`‖p_x v‖ ≤ ‖v‖`, and if `x ↦ p_x` is `μ_V`-a.e. strongly measurable, then on each `S` with
`μ_V(S) < ∞` the functions `x ↦ ⟨p_x e, p_x g(x)⟩` (`g` a.e. strongly measurable, `‖g‖ ≤ C`) and
`x ↦ |p_x − p_T|²` are `μ_V`-integrable.  `p_x` is an orthogonal projection or `0`; each integrand
is a continuous function of `(p_x, g(x))`, resp. of `p_x`, bounded by `‖e‖ C`, resp. `4 (n + ℓ)`. -/
theorem gte_tangentProj_integrands : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), (∀ x v : Amb n ℓ, ‖V.tangentProj x v‖ ≤ ‖v‖) ∧ (AEStronglyMeasurable V.tangentProj V.weight → ∀ S : Set (Amb n ℓ), V.weight S < ⊤ → (∀ (e : Amb n ℓ) (g : Amb n ℓ → Amb n ℓ) (C : ℝ), AEStronglyMeasurable g V.weight → (∀ x, ‖g x‖ ≤ C) → IntegrableOn (fun x => inner ℝ (V.tangentProj x e) (V.tangentProj x (g x))) S V.weight) ∧ ∀ T : Submodule ℝ (Amb n ℓ), IntegrableOn (fun x => hsNormSq (V.tangentProj x - T.starProjection)) S V.weight) := by
  intro n ℓ U V
  -- Step 1, (a): `p_x` is `K.starProjection` (operator norm `≤ 1`) or `0`.
  have ha : ∀ x v : Amb n ℓ, ‖V.tangentProj x v‖ ≤ ‖v‖ := by
    intro x v
    unfold RectifiableVarifold.tangentProj
    split_ifs with h
    · calc ‖(Classical.choose h).starProjection v‖
          ≤ ‖(Classical.choose h).starProjection‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖v‖ := by gcongr; exact Submodule.starProjection_norm_le _
        _ = ‖v‖ := one_mul _
    · simp
  -- Step 2: `x ↦ p_x` is a.e. strongly measurable and `μ_V(S) < ∞`.
  refine ⟨ha, fun hmeas S hS => ⟨?_, ?_⟩⟩
  · intro e g C hg hC
    -- Step 3: `(L, w) ↦ ⟨L e, L w⟩` is continuous, so the integrand is a.e. strongly measurable.
    have hcont : Continuous (fun (L : Amb n ℓ →L[ℝ] Amb n ℓ) (w : Amb n ℓ) =>
        inner ℝ (L e) (L w)).uncurry :=
      (continuous_fst.clm_apply continuous_const).inner (continuous_fst.clm_apply continuous_snd)
    -- Steps 4–5: the integrand is bounded by `‖e‖ C` (Cauchy–Schwarz and (a)).
    refine Measure.integrableOn_of_bounded (M := ‖e‖ * C) hS.ne
      (hcont.comp_aestronglyMeasurable₂ hmeas hg) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    calc |inner ℝ (V.tangentProj x e) (V.tangentProj x (g x))|
        ≤ ‖V.tangentProj x e‖ * ‖V.tangentProj x (g x)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖e‖ * C :=
        mul_le_mul (ha x e) ((ha x (g x)).trans (hC x)) (norm_nonneg _) (norm_nonneg _)
  · intro T
    -- Step 6: `A ↦ hsNormSq A = Σᵢ ‖A eᵢ‖²` is continuous, so the integrand is a.e. strongly
    -- measurable.
    have hcont : Continuous (fun A : Amb n ℓ →L[ℝ] Amb n ℓ => hsNormSq A) := by
      unfold hsNormSq
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_id.clm_apply continuous_const).norm).pow 2
    -- Steps 7–8: `0 ≤ hsNormSq (p_x − P_T) ≤ 4 (n + ℓ)`, since `‖(p_x − P_T) eᵢ‖ ≤ 2`.
    refine Measure.integrableOn_of_bounded (M := 4 * (n + ℓ)) hS.ne
      (hcont.comp_aestronglyMeasurable (hmeas.sub aestronglyMeasurable_const))
      (Eventually.of_forall fun x => ?_)
    have hnn : 0 ≤ hsNormSq (V.tangentProj x - T.starProjection) := by
      unfold hsNormSq; positivity
    rw [Real.norm_of_nonneg hnn]
    unfold hsNormSq
    have hterm : ∀ i : Fin (n + ℓ),
        ‖(V.tangentProj x - T.starProjection) (EuclideanSpace.single i 1)‖ ^ 2 ≤ 4 := by
      intro i
      have h1 : ‖(EuclideanSpace.single i (1 : ℝ) : Amb n ℓ)‖ = 1 := by simp
      have hp : ‖V.tangentProj x (EuclideanSpace.single i 1)‖ ≤ 1 := (ha x _).trans h1.le
      have hq : ‖T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ≤ 1 :=
        calc ‖T.starProjection (EuclideanSpace.single i (1 : ℝ))‖
            ≤ ‖T.starProjection‖ * ‖(EuclideanSpace.single i (1 : ℝ) : Amb n ℓ)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * 1 := by rw [h1]; gcongr; exact Submodule.starProjection_norm_le _
          _ = 1 := one_mul _
      have hd : ‖(V.tangentProj x - T.starProjection) (EuclideanSpace.single i 1)‖ ≤ 2 := by
        rw [sub_apply]
        calc _ ≤ ‖V.tangentProj x (EuclideanSpace.single i 1)‖
              + ‖T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add hp hq
          _ = 2 := by norm_num
      have h0 := norm_nonneg ((V.tangentProj x - T.starProjection) (EuclideanSpace.single i 1))
      nlinarith
    calc ∑ i : Fin (n + ℓ), ‖(V.tangentProj x - T.starProjection) (EuclideanSpace.single i 1)‖ ^ 2
        ≤ ∑ _i : Fin (n + ℓ), (4 : ℝ) := Finset.sum_le_sum fun i _ => hterm i
      _ = 4 * (n + ℓ) := by simp [Finset.sum_const, Finset.card_univ]; ring
/-- Graph coordinates for the graph tangential estimate (steps 1(i), 1(ii) and 2(iii) of its proof,
for Simon Ch. 5, Theorem 4.5, displays (8)–(12)).  With `E = EuclideanSpace.finAddEquivProd` and
`a(z) = (E (q⁻¹ z)).1`: (i) `(x, y) ↦ graphPoint x y` is continuous; (ii) `a` is continuous;
(iii) `a(q(x, y)) = x`; (iv) if `f` is continuous on `B_R(0)` and `r ≤ R`, then
`q(graph f|B_R(0))` is compact and `q(graph f|B̆_r(0))` is Borel.  Comparing coordinates
(`Fin.addCases`), `graphPoint x y = E⁻¹(x, y)`, which gives (i)–(iii).  `q(graph f|B_R(0))` is the
image of the compact ball under `F x = q(x, f x)`, continuous on it; by (iii) and `r ≤ R`,
`q(graph f|B̆_r(0)) = q(graph f|B_R(0)) ∩ a⁻¹(B̆_r(0))`, the intersection of a closed and an open
set. -/
theorem gte_graph_image_geometry : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), Continuous (fun p : Rn n × Rn ℓ => graphPoint p.1 p.2) ∧ Continuous (fun z : Amb n ℓ => (EuclideanSpace.finAddEquivProd (q.symm z)).1) ∧ (∀ (x : Rn n) (y : Rn ℓ), (EuclideanSpace.finAddEquivProd (q.symm (q (graphPoint x y)))).1 = x) ∧ ∀ (f : Rn n → Rn ℓ) (R r : ℝ), ContinuousOn f (closedBall 0 R) → r ≤ R → IsCompact (q '' graphOver f (closedBall 0 R)) ∧ MeasurableSet (q '' graphOver f (ball 0 r)) := by
  intro n ℓ q
  -- Step 1: `graphPoint x y = E⁻¹(x, y)`, comparing coordinates.
  have hgp : ∀ (x : Rn n) (y : Rn ℓ), graphPoint x y =
      (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm (x, y) := by
    intro x y
    ext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp [graphPoint]
    · simp [graphPoint]
  -- Step 2, (i): `(x, y) ↦ graphPoint x y` is the continuous map `E⁻¹`.
  have hi : Continuous (fun p : Rn n × Rn ℓ => graphPoint p.1 p.2) := by
    have : (fun p : Rn n × Rn ℓ => graphPoint p.1 p.2) =
        (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm := by
      funext p
      exact hgp p.1 p.2
    rw [this]
    exact ContinuousLinearEquiv.continuous _
  -- Step 3, (ii): `a = Prod.fst ∘ E ∘ q⁻¹`.
  have hii : Continuous (fun z : Amb n ℓ => (EuclideanSpace.finAddEquivProd (q.symm z)).1) :=
    continuous_fst.comp ((ContinuousLinearEquiv.continuous _).comp q.symm.continuous)
  -- Step 4, (iii): `a(q(x, y)) = (E (E⁻¹(x, y))).1 = x`.
  have hiii : ∀ (x : Rn n) (y : Rn ℓ),
      (EuclideanSpace.finAddEquivProd (q.symm (q (graphPoint x y)))).1 = x := by
    intro x y
    rw [LinearIsometryEquiv.symm_apply_apply, hgp, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨hi, hii, hiii, ?_⟩
  intro f R r hf hrR
  -- Step 5, (iv) compactness: `q '' graphOver f D = F '' D`, and `F` is continuous on the compact
  -- ball `B_R(0)`.
  have himg : ∀ D : Set (Rn n), q '' graphOver f D = (fun x => q (graphPoint x (f x))) '' D := by
    intro D
    unfold graphOver
    rw [Set.image_image]
  have hFcont : ContinuousOn (fun x => q (graphPoint x (f x))) (closedBall 0 R) :=
    q.continuous.comp_continuousOn (hi.comp_continuousOn (continuousOn_id.prodMk hf))
  have hcpt : IsCompact (q '' graphOver f (closedBall 0 R)) := by
    rw [himg]
    exact (isCompact_closedBall 0 R).image_of_continuousOn hFcont
  refine ⟨hcpt, ?_⟩
  -- Step 6, (iv) Borel: `F(B̆_r(0)) = F(B_R(0)) ∩ a⁻¹(B̆_r(0))` by (iii) and `r ≤ R`.
  have heq : q '' graphOver f (ball 0 r) =
      q '' graphOver f (closedBall 0 R) ∩
        (fun z : Amb n ℓ => (EuclideanSpace.finAddEquivProd (q.symm z)).1) ⁻¹' ball 0 r := by
    rw [himg, himg]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR)) hx, rfl⟩, ?_⟩
      show (EuclideanSpace.finAddEquivProd (q.symm (q (graphPoint x (f x))))).1 ∈ ball 0 r
      rw [hiii]
      exact hx
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      refine ⟨x, ?_, rfl⟩
      have hz' : (EuclideanSpace.finAddEquivProd (q.symm (q (graphPoint x (f x))))).1 ∈ ball 0 r :=
        hz
      rwa [hiii] at hz'
  rw [heq]
  exact hcpt.isClosed.measurableSet.inter (isOpen_ball.preimage hii).measurableSet
/-- A map `f : ℝⁿ → ℝ^ℓ` that is `K`-Lipschitz on the closed ball `B_R(0)` (graph estimates in the
proof of Simon Ch. 5, Theorem 4.5, displays (8)–(12), pp. 118–119): the set of points of the open
ball `B̆_R(0)` where `f` is not differentiable is Borel and `Lⁿ`-null (Rademacher's theorem),
`‖Df(x)‖ ≤ K` on `B̆_R(0)`, and where `f` is differentiable the gradient of the coordinate
`fʲ = (y ↦ f(y)ⱼ)` represents the `j`-th row of `Df(x)`: `⟨∇fʲ(x), v⟩ = (Df(x) v)ⱼ`. -/
theorem gte_lipschitz_ball_calculus : ∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (K : ℝ≥0) (R : ℝ), LipschitzOnWith K f (closedBall 0 R) → MeasurableSet (ball (0 : Rn n) R ∩ {x | ¬DifferentiableAt ℝ f x}) ∧ volume (ball (0 : Rn n) R ∩ {x | ¬DifferentiableAt ℝ f x}) = 0 ∧ ∀ x ∈ ball (0 : Rn n) R, ‖fderiv ℝ f x‖ ≤ K ∧ (DifferentiableAt ℝ f x → ∀ (j : Fin ℓ) (v : Rn n), inner ℝ (gradient (fun y => f y j) x) v = fderiv ℝ f x v j) := by
  intro n ℓ f K R hf
  -- (i): the differentiability set of any map into a complete space is Borel
  refine ⟨measurableSet_ball.inter (measurableSet_of_differentiableAt ℝ f).compl, ?_, ?_⟩
  -- (ii): Rademacher on the open ball, where differentiability within it is differentiability
  · have hae := (hf.mono ball_subset_closedBall).ae_differentiableWithinAt_of_mem
      (μ := (volume : Measure (Rn n)))
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with x hx hxZ
    exact hxZ.2 ((hx hxZ.1).differentiableAt (isOpen_ball.mem_nhds hxZ.1))
  · intro x hx
    -- (iii): `B_R(0)` is a neighbourhood of `x` on which `f` is `K`-Lipschitz
    refine ⟨norm_fderiv_le_of_lipschitzOn ℝ
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) hf, ?_⟩
    -- gradient rows: `fʲ = proj_j ∘ f`, the chain rule, and `⟪(toDual)⁻¹ L, v⟫ = L v`
    intro hfx j v
    have hd : HasFDerivAt (fun y => f y j)
        ((EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).comp (fderiv ℝ f x)) x :=
      (EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).hasFDerivAt.comp x hfx.hasFDerivAt
    rw [inner_gradient_left, hd.fderiv]
    rfl
/-- **Simon Ch. 5, proof of Theorem 4.5, displays (8)–(12) (pp. 118–119)**, localization step in an
abstract measure space.  If `Φ` is integrable on `B`, `|Φ| ≤ M` everywhere, `Φ` vanishes on
`(B \ G') ∩ G`, `μ((B \ G') \ G) ≤ m < ∞`, and `|Φ − φ| ≤ M ψ` a.e. on `G' ⊆ B ∩ B'` with `ψ ≥ 0`
integrable on `B'`, then `|∫_{G'} φ| ≤ |∫_B Φ| + M m + M ∫_{B'} ψ`.
Proof: splitting `∫_B Φ` along `G'` and then along `G` gives `∫_{G'} Φ = ∫_B Φ − ∫_{(B \ G') \ G} Φ`,
and the last integral is at most `M μ((B \ G') \ G) ≤ M m` in absolute value.  On `G'`, `Φ − φ` is
dominated by `M ψ`, so `φ` is integrable there and `|∫_{G'} Φ − ∫_{G'} φ| ≤ M ∫_{G'} ψ ≤ M ∫_{B'} ψ`;
conclude by the triangle inequality. -/
theorem gte_localized_comparison : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (B B' G G' : Set X) (Φ φ ψ : X → ℝ) (M : ℝ) (m : ℝ≥0∞), 0 ≤ M → MeasurableSet G → MeasurableSet G' → G' ⊆ B → G' ⊆ B' → IntegrableOn Φ B μ → (∀ x, |Φ x| ≤ M) → (∀ x ∈ (B \ G') ∩ G, Φ x = 0) → μ ((B \ G') \ G) ≤ m → m < ⊤ → AEStronglyMeasurable φ (μ.restrict G') → IntegrableOn ψ B' μ → (∀ x, 0 ≤ ψ x) → (∀ᵐ x ∂μ, x ∈ G' → |Φ x - φ x| ≤ M * ψ x) → |∫ x in G', φ x ∂μ| ≤ |∫ x in B, Φ x ∂μ| + M * m.toReal + M * ∫ x in B', ψ x ∂μ := by
  intro X _ μ B B' G G' Φ φ ψ M m hM hG hG' hG'B hG'B' hΦ hΦM hΦ0 hμm hm hφ hψ hψ0 hcmp
  -- Steps 1–3: split `∫_B Φ` along `G'` (`B ∩ G' = G'`) and then `∫_{B \ G'} Φ` along `G`; the
  -- `(B \ G') ∩ G` part vanishes, so `∫_{G'} Φ = ∫_B Φ − ∫_{(B \ G') \ G} Φ`.
  have h1 : ∫ x in B ∩ G', Φ x ∂μ + ∫ x in B \ G', Φ x ∂μ = ∫ x in B, Φ x ∂μ :=
    integral_inter_add_sdiff hG' hΦ
  rw [inter_eq_right.mpr hG'B] at h1
  have h2 : ∫ x in (B \ G') ∩ G, Φ x ∂μ + ∫ x in (B \ G') \ G, Φ x ∂μ =
      ∫ x in B \ G', Φ x ∂μ :=
    integral_inter_add_sdiff hG (hΦ.mono_set sdiff_subset)
  rw [setIntegral_eq_zero_of_forall_eq_zero hΦ0, zero_add] at h2
  -- Step 4: the off part is at most `M μ((B \ G') \ G) ≤ M m` in absolute value.
  have h4 : |∫ x in (B \ G') \ G, Φ x ∂μ| ≤ M * m.toReal := by
    have h := norm_setIntegral_le_of_norm_le_const (hμm.trans_lt hm)
      (fun x _ => (Real.norm_eq_abs (Φ x)).le.trans (hΦM x))
    rw [Real.norm_eq_abs, measureReal_def] at h
    exact h.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hm.ne hμm) hM)
  -- Step 5: `Φ − φ` is dominated by `M ψ` on `G'`, so `φ = Φ − (Φ − φ)` is integrable on `G'`.
  have hΦG' : Integrable Φ (μ.restrict G') := (hΦ.mono_set hG'B).integrable
  have hψG' : Integrable (fun x => M * ψ x) (μ.restrict G') :=
    (hψ.mono_set hG'B').integrable.const_mul M
  have hae : ∀ᵐ x ∂μ.restrict G', ‖Φ x - φ x‖ ≤ M * ψ x := by
    rw [ae_restrict_iff' hG']
    filter_upwards [hcmp] with x hx hxG'
    rw [Real.norm_eq_abs]
    exact hx hxG'
  have hdiff : Integrable (fun x => Φ x - φ x) (μ.restrict G') :=
    hψG'.mono' (hΦG'.aestronglyMeasurable.sub hφ) hae
  have hφG' : Integrable φ (μ.restrict G') :=
    (hΦG'.sub hdiff).congr (Eventually.of_forall fun x => sub_sub_cancel (Φ x) (φ x))
  -- Step 6: `|∫_{G'} Φ − ∫_{G'} φ| = |∫_{G'} (Φ − φ)| ≤ M ∫_{G'} ψ ≤ M ∫_{B'} ψ`.
  have h6 : |∫ x in G', Φ x ∂μ - ∫ x in G', φ x ∂μ| ≤ M * ∫ x in B', ψ x ∂μ := by
    rw [← integral_sub hΦG' hφG', ← Real.norm_eq_abs]
    calc ‖∫ x in G', (Φ x - φ x) ∂μ‖ ≤ ∫ x in G', M * ψ x ∂μ :=
          norm_integral_le_of_norm_le hψG' hae
      _ = M * ∫ x in G', ψ x ∂μ := integral_const_mul M _
      _ ≤ M * ∫ x in B', ψ x ∂μ :=
          mul_le_mul_of_nonneg_left (setIntegral_mono_set hψ (Eventually.of_forall hψ0)
            (Eventually.of_forall hG'B')) hM
  -- Step 7: the triangle inequality.
  have hI := le_abs_self (∫ x in B, Φ x ∂μ)
  have hI' := neg_abs_le (∫ x in B, Φ x ∂μ)
  obtain ⟨h4l, h4r⟩ := abs_le.mp h4
  obtain ⟨h6l, h6r⟩ := abs_le.mp h6
  exact abs_le.mpr ⟨by linarith, by linarith⟩
/-- The linear algebra in the proof of Simon Ch. 5, Lemma 2.1 (p. 107): (i) the operator norm of a
linear map is at most its Hilbert–Schmidt norm `|A|`; (ii) `|p_{T⊥} v| = dist(v, T)`; and
(iii) display (2) of the proof, `trace(p_{T⊥} ∘ p_P) = ½ |p_P − p_T|²` when `dim P = dim T`. -/
theorem hsNorm_starProjection_trace_identities : (∀ (m k : ℕ) (A : Rn m →L[ℝ] Rn k), ‖A‖ ≤ hsNorm A) ∧ (∀ (m : ℕ) (T : Submodule ℝ (Rn m)) (v : Rn m), ‖Tᗮ.starProjection v‖ = Metric.infDist v (T : Set (Rn m))) ∧ ∀ (m : ℕ) (P T : Submodule ℝ (Rn m)), Module.finrank ℝ P = Module.finrank ℝ T → LinearMap.trace ℝ (Rn m) (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) = hsNormSq (P.starProjection - T.starProjection) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- (i) `‖A v‖ ≤ Σᵢ |vᵢ| ‖A eᵢ‖ ≤ ‖v‖ |A|` by the triangle and Cauchy–Schwarz inequalities.
    intro m k A
    refine A.opNorm_le_bound (Real.sqrt_nonneg _) fun v => ?_
    have hv : ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
      simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
    calc ‖A v‖ = ‖A (∑ i, v i • EuclideanSpace.single i (1 : ℝ))‖ := by rw [hv]
      _ = ‖∑ i, v i • A (EuclideanSpace.single i 1)‖ := by simp only [map_sum, map_smul]
      _ ≤ ∑ i, ‖v i‖ * ‖A (EuclideanSpace.single i 1)‖ :=
          (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_smul _ _)
      _ ≤ √(∑ i, ‖v i‖ ^ 2) * √(∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = hsNorm A * ‖v‖ := by rw [EuclideanSpace.norm_eq v, mul_comm (hsNorm A)]; rfl
  · -- (ii) `p_{T⊥} v = v − p_T v`, and `p_T v` is the point of `T` nearest to `v`.
    intro m T v
    rw [Submodule.starProjection_orthogonal_val, ← dist_eq_norm,
      Submodule.dist_starProjection_eq_infDist]
  · -- (iii) Compute both sides in the standard orthonormal basis `eᵢ`.
    intro m P T hPT
    -- The trace is the sum of the diagonal entries `⟪eᵢ, f eᵢ⟫`.
    have htr : ∀ f : Rn m →ₗ[ℝ] Rn m, LinearMap.trace ℝ (Rn m) f =
        ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ)) (f (EuclideanSpace.single i 1)) := by
      intro f
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin m) ℝ).toBasis f,
        Matrix.trace]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply]
    -- The trace of an orthogonal projection is the dimension of its range.
    have hproj : ∀ W : Submodule ℝ (Rn m),
        LinearMap.trace ℝ (Rn m) W.starProjection.toLinearMap = Module.finrank ℝ W := fun W =>
      LinearMap.IsProj.trace
        ⟨W.starProjection_apply_mem, fun _ hx => W.starProjection_eq_self_iff.2 hx⟩
    -- `‖p_W x‖² = ⟪x, p_W x⟫`, since `p_W` is self-adjoint and idempotent.
    have hsq : ∀ (W : Submodule ℝ (Rn m)) (x : Rn m),
        ‖W.starProjection x‖ ^ 2 = inner ℝ x (W.starProjection x) := by
      intro W x
      rw [← real_inner_self_eq_norm_sq, W.inner_starProjection_left_eq_right,
        W.starProjection_eq_self_iff.2 (W.starProjection_apply_mem x)]
    -- Pointwise, `2 ⟪x, (I − q) p x⟫ = ‖(p − q) x‖² + ⟪x, p x⟫ − ⟪x, q x⟫`.
    have hterm : ∀ x : Rn m, 2 * inner ℝ x (Tᗮ.starProjection (P.starProjection x)) =
        ‖(P.starProjection - T.starProjection) x‖ ^ 2 + inner ℝ x (P.starProjection x) -
          inner ℝ x (T.starProjection x) := by
      intro x
      rw [Submodule.starProjection_orthogonal_val, sub_apply, norm_sub_sq_real, hsq P, hsq T,
        inner_sub_right, ← T.inner_starProjection_left_eq_right,
        real_inner_comm (T.starProjection x)]
      ring
    -- `trace p_P = dim P = dim T = trace p_T`.
    have hdim : ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (P.starProjection (EuclideanSpace.single i 1)) =
        ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (T.starProjection (EuclideanSpace.single i 1)) := by
      have h := hproj P
      rw [hPT, ← hproj T, htr, htr] at h
      exact h
    rw [htr, hsNormSq, eq_div_iff two_ne_zero, mul_comm, Finset.mul_sum]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [Finset.sum_congr rfl fun i _ => hterm (EuclideanSpace.single i 1), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hdim, add_sub_cancel_right]
/-- Graph coordinates on `ℝ^{n+ℓ} = ℝⁿ × ℝ^ℓ`, used for the graph estimates behind Simon Ch. 5,
Remark 5.3 (p. 122): the point `(a, b) = graphPoint a b` has coordinate `a_i` at `castAdd ℓ i` and
`b_j` at `natAdd n j`; `(a, b)` is linear in the pair; `|(a, b)|² = |a|² + |b|²`; and
`⟨(a, b), (a', b')⟩ = ⟨a, a'⟩ + ⟨b, b'⟩`.
Every index of `Fin (n + ℓ)` is `castAdd ℓ i` or `natAdd n j` (`Fin.addCases`), so the linearity
identities hold coordinatewise, and the norm and the inner product split as sums over the two
blocks of indices (`Fin.sum_univ_add`). -/
theorem any_radius_gr_la_graphPoint_algebra : ∀ (n ℓ : ℕ), (∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i) ∧ (∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j) ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint (a + a') (b + b') = graphPoint a b + graphPoint a' b') ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint (a - a') (b - b') = graphPoint a b - graphPoint a' b') ∧ (∀ (t : ℝ) (a : Rn n) (b : Rn ℓ), graphPoint (t • a) (t • b) = t • graphPoint a b) ∧ (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), inner ℝ (graphPoint a b) (graphPoint a' b') = inner ℝ a a' + inner ℝ b b') := by
  intro n ℓ
  -- (C1), (C2): the coordinates of `graphPoint a b = toLp (Fin.append a b)`
  have hC1 : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp only [graphPoint, PiLp.toLp_apply, Fin.append_left]
  have hC2 : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp only [graphPoint, PiLp.toLp_apply, Fin.append_right]
  refine ⟨hC1, hC2, ?_, ?_, ?_, ?_, ?_⟩
  -- (L1)–(L3): compare the coordinates at every `castAdd ℓ i` and every `natAdd n j`
  · intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.add_apply, hC1]
    · simp only [PiLp.add_apply, hC2]
  · intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.sub_apply, hC1]
    · simp only [PiLp.sub_apply, hC2]
  · intro t a b
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.smul_apply, hC1]
    · simp only [PiLp.smul_apply, hC2]
  -- (L4): split `‖x‖² = Σ_k ‖x_k‖²` over the two blocks of indices
  · intro a b
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp only [hC1, hC2]
  -- (IP): split `⟪x, y⟫ = Σ_k ⟪x_k, y_k⟫` in the same way
  · intro a a' b b'
    rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_add]
    simp only [hC1, hC2]
/-- The rotated plane `T₀ = q(ℝⁿ × {0})` of Simon Ch. 5, Lemma 2.6 (p. 110), in the graph estimates
behind Remark 5.3 (p. 122): for a linear isometry `q` of `ℝ^{n+ℓ}`, (L5) `p_{T₀}(q(a, b)) = q(a, 0)`,
(L6) `dist(q(a, b), T₀) = |b|` and (L7) `dim T₀ = n`.
Since `e_{castAdd ℓ i} = (eᵢ, 0)` and `c ↦ (c, 0)` is linear, `ℝⁿ × {0} = {(c, 0) : c ∈ ℝⁿ}`, which
is orthogonal to `(0, b)`; as `q` preserves inner products, `q(a, 0) ∈ T₀` and
`q(a, b) − q(a, 0) = q(0, b) ⊥ T₀` characterize the projection, and the distance to `T₀` is attained
at the projection.  The `e_{castAdd ℓ i}` are independent and `q` preserves dimension. -/
theorem any_radius_gr_la_rotatedPlane_facts : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (a : Rn n) (b : Rn ℓ), (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a (0 : Rn ℓ))) ∧ (∀ (a : Rn n) (b : Rn ℓ), infDist (q (graphPoint a b)) (rotatedPlane q : Set (Amb n ℓ)) = ‖b‖) ∧ Module.finrank ℝ (rotatedPlane q) = n := by
  intro n ℓ q
  -- (C1), (C2), (L1)–(L4) and (IP) for `graphPoint`
  obtain ⟨hC1, hC2, hadd, hsub, hsmul, hnorm, hinner⟩ :=
    Submission.any_radius_gr_la_graphPoint_algebra n ℓ
  -- Step 1: `e_{castAdd ℓ i} = (eᵢ, 0)`; compare the coordinates at `castAdd ℓ i'` and `natAdd n j`
  have hbasis : ∀ i : Fin n, EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) =
      graphPoint (EuclideanSpace.single i (1 : ℝ)) (0 : Rn ℓ) := by
    intro i
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) k
    · rw [hC1]
      simp only [PiLp.single_apply, (Fin.castAdd_injective n ℓ).eq_iff]
    · rw [hC2]
      have hne : Fin.natAdd n j ≠ Fin.castAdd ℓ i := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
        omega
      simp [hne]
  -- Step 2: `G c = (c, 0)` is linear, by (L1) and (L3)
  let G : Rn n →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun c => graphPoint c (0 : Rn ℓ)
      map_add' := fun c c' => by simpa using hadd c c' (0 : Rn ℓ) (0 : Rn ℓ)
      map_smul' := fun t c => by simpa using hsmul t c (0 : Rn ℓ) }
  -- Step 3: `ℝⁿ × {0} = {(c, 0) : c ∈ ℝⁿ}`, the image under `G` of the span of the `eᵢ`
  have hhor : horizontalPlane n ℓ = LinearMap.range G := by
    have hfun : (fun i : Fin n => EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ)) =
        G ∘ fun i : Fin n => EuclideanSpace.single i (1 : ℝ) := by
      funext i
      exact hbasis i
    have hspan :
        Submodule.span ℝ (Set.range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) = ⊤ := by
      have hb : ⇑(EuclideanSpace.basisFun (Fin n) ℝ) = fun i => EuclideanSpace.single i (1 : ℝ) :=
        funext (EuclideanSpace.basisFun_apply (Fin n) ℝ)
      have := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq
      rwa [OrthonormalBasis.coe_toBasis, hb] at this
    rw [horizontalPlane, hfun, Set.range_comp, Submodule.span_image, hspan,
      LinearMap.range_eq_map]
  -- Step 4: `(0, b)` is orthogonal to `ℝⁿ × {0}`, by (IP)
  have horth : ∀ (b : Rn ℓ), ∀ h ∈ horizontalPlane n ℓ,
      inner ℝ (graphPoint (0 : Rn n) b) h = 0 := by
    intro b h hh
    rw [hhor] at hh
    obtain ⟨c, rfl⟩ := hh
    show inner ℝ (graphPoint 0 b) (graphPoint c 0) = 0
    rw [hinner]
    simp
  -- Step 6(ii): `q(a, b) − q(a, 0) = q(0, b)`, by (L2)
  have hdiff : ∀ (a : Rn n) (b : Rn ℓ),
      q (graphPoint a b) - q (graphPoint a 0) = q (graphPoint 0 b) := by
    intro a b
    rw [← map_sub, ← hsub]
    simp
  -- Step 6, (L5): `q(a, 0) ∈ T₀` and `q(a, b) − q(a, 0) ⊥ T₀`, as `q` preserves inner products
  have hproj : ∀ (a : Rn n) (b : Rn ℓ),
      (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a (0 : Rn ℓ)) := by
    intro a b
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact Submodule.mem_map_of_mem (by rw [hhor]; exact ⟨a, rfl⟩)
    · intro w hw
      obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hw
      rw [hdiff]
      simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
      rw [LinearIsometryEquiv.inner_map_map]
      exact horth b h hh
  refine ⟨hproj, ?_, ?_⟩
  -- Step 8, (L6): `dist(v, T₀) = |v − p_{T₀} v| = |q(0, b)| = |(0, b)| = |b|`, by (L5) and (L4)
  · intro a b
    rw [← Submodule.dist_starProjection_eq_infDist, hproj, dist_eq_norm, hdiff,
      LinearIsometryEquiv.norm_map]
    have h := hnorm 0 b
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  -- Step 9, (L7): the `e_{castAdd ℓ i}` are independent, and `q` preserves `finrank`
  · have hli : LinearIndependent ℝ
        (fun i : Fin n => EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ)) :=
      (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (n + ℓ))).linearIndependent.comp _
        (Fin.castAdd_injective n ℓ)
    rw [rotatedPlane, LinearEquiv.finrank_map_eq, horizontalPlane, finrank_span_eq_card hli,
      Fintype.card_fin]
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

/-- A step in the proof of Simon Ch. 5, Theorem 4.5 (displays (10)–(11)): for `u, w ∈ T`,
`|⟪p_S u, p_S w⟫ − ⟪u, w⟫| ≤ |p_S − p_T|² |u| |w|`, with `|p_S − p_T|` the Hilbert–Schmidt norm. -/
theorem gwe_gta_proj_inner_defect : ∀ (m : ℕ) (S T : Submodule ℝ (Rn m)) (u w : Rn m), u ∈ T → w ∈ T → |inner ℝ (S.starProjection u) (S.starProjection w) - inner ℝ u w| ≤ hsNormSq (S.starProjection - T.starProjection) * (‖u‖ * ‖w‖) := by
  intro m S T u w hu hw
  -- `p_T` fixes `u, w ∈ T`, so `(p_S − p_T) x = p_S x − x` for `x = u, w`.
  have hfix : ∀ x ∈ T, (S.starProjection - T.starProjection) x = S.starProjection x - x :=
    fun x hx => by rw [sub_apply, T.starProjection_eq_self_iff.2 hx]
  -- `p_S` is self-adjoint and idempotent, so `⟪p_S u, p_S w⟫ = ⟪u, p_S w⟫ = ⟪p_S u, w⟫`; hence
  -- `⟪p_S u, p_S w⟫ − ⟪u, w⟫ = −⟪(p_S − p_T) u, (p_S − p_T) w⟫`.
  have hid : inner ℝ (S.starProjection u) (S.starProjection w) - inner ℝ u w =
      -inner ℝ ((S.starProjection - T.starProjection) u)
        ((S.starProjection - T.starProjection) w) := by
    have h1 := S.inner_starProjection_left_eq_right u (S.starProjection w)
    have h2 := S.inner_starProjection_left_eq_right u w
    rw [S.starProjection_eq_self_iff.2 (S.starProjection_apply_mem w)] at h1
    rw [hfix u hu, hfix w hw, inner_sub_left, inner_sub_right, inner_sub_right]
    linarith
  -- `|⟪A x, A y⟫| ≤ ‖A x‖ ‖A y‖ ≤ ‖A‖² ‖x‖ ‖y‖ ≤ |A|² ‖x‖ ‖y‖`, since `‖A‖ ≤ |A|`.
  have key : ∀ (A : Rn m →L[ℝ] Rn m) (x y : Rn m),
      |inner ℝ (A x) (A y)| ≤ hsNormSq A * (‖x‖ * ‖y‖) := by
    intro A x y
    have hA : ‖A‖ ^ 2 ≤ hsNormSq A :=
      (Real.le_sqrt (norm_nonneg A) (Finset.sum_nonneg fun i _ => sq_nonneg _)).1
        (hsNorm_starProjection_trace_identities.1 m m A)
    calc |inner ℝ (A x) (A y)| ≤ ‖A x‖ * ‖A y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖x‖ * (‖A‖ * ‖y‖) :=
          mul_le_mul (A.le_opNorm x) (A.le_opNorm y) (norm_nonneg _) (by positivity)
      _ = ‖A‖ ^ 2 * (‖x‖ * ‖y‖) := by ring
      _ ≤ hsNormSq A * (‖x‖ * ‖y‖) := by gcongr
  rw [hid, abs_neg]
  exact key _ u w
/-- Display 4.2 of Simon Ch. 5 (p. 115) for a rotated plane, as used in (9)–(13) of the proof of
Theorem 4.5: if `S ⊆ ℝ^{n+ℓ}` is an `n`-dimensional subspace and `T = q(ℝⁿ × {0})`, then
`Σ_j |p_S e'_j|² = ½ |p_S − p_T|²`, where `e'_j = q(0, d_j)` are the images under `q` of the last
`ℓ` standard basis vectors.
In the orthonormal basis `q(ε_k)`, `trace(p_{T⊥} ∘ p_S) = Σ_k ⟨p_{T⊥} q(ε_k), p_S q(ε_k)⟩`.  The
horizontal vectors `q(eᵢ, 0)` lie in `T` and contribute `0`, while `p_{T⊥} e'_j = e'_j` and
`⟨e'_j, p_S e'_j⟩ = |p_S e'_j|²`; finally `trace(p_{T⊥} ∘ p_S) = ½ |p_S − p_T|²` since
`dim S = n = dim T`. -/
theorem gwe_gta_vertical_trace_sum : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (S : Submodule ℝ (Amb n ℓ)), Module.finrank ℝ S = n → ∑ j : Fin ℓ, ‖S.starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ ^ 2 = hsNormSq (S.starProjection - (rotatedPlane q).starProjection) / 2 := by
  intro n ℓ q S hS
  -- (C1), (C2) and (L3) for `graphPoint`; (L5) and (L7) for `T = q(ℝⁿ × {0})`
  obtain ⟨hC1, hC2, -, -, hsmul, -, -⟩ := Submission.any_radius_gr_la_graphPoint_algebra n ℓ
  obtain ⟨hproj, -, hdimT⟩ := Submission.any_radius_gr_la_rotatedPlane_facts n ℓ q
  -- Step 2: `ε_{castAdd ℓ i} = (eᵢ, 0)` and `ε_{natAdd n j} = (0, d_j)`, coordinatewise
  have hcast : ∀ i : Fin n, EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) =
      graphPoint (EuclideanSpace.single i (1 : ℝ)) (0 : Rn ℓ) := by
    intro i
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
    · rw [hC1, PiLp.single_apply, PiLp.single_apply]
      simp [Fin.castAdd_inj]
    · rw [hC2, PiLp.single_apply]
      have hne : Fin.natAdd n j' ≠ Fin.castAdd ℓ i := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
        omega
      simp [hne]
  have hnat : ∀ j : Fin ℓ, EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ) =
      graphPoint (0 : Rn n) (EuclideanSpace.single j (1 : ℝ)) := by
    intro j
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
    · rw [hC1, PiLp.single_apply]
      have hne : Fin.castAdd ℓ i' ≠ Fin.natAdd n j := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
        omega
      simp [hne]
    · rw [hC2, PiLp.single_apply, PiLp.single_apply]
      simp [Fin.natAdd_inj]
  -- Step 3: `(0, 0) = 0`, by (L3) with `t = 0`
  have hzero : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    simpa using hsmul 0 0 0
  -- Steps 4–5: in the orthonormal basis `b_k = q(ε_k)`, `trace f = Σ_k ⟨b_k, f b_k⟩`
  let b : OrthonormalBasis (Fin (n + ℓ)) ℝ (Amb n ℓ) :=
    (EuclideanSpace.basisFun (Fin (n + ℓ)) ℝ).map q
  have hb : ∀ k, b k = q (EuclideanSpace.single k 1) := by
    intro k
    simp [b, EuclideanSpace.basisFun_apply]
  have htrace : ∀ f : Amb n ℓ →ₗ[ℝ] Amb n ℓ,
      LinearMap.trace ℝ (Amb n ℓ) f = ∑ k, inner ℝ (b k) (f (b k)) := by
    intro f
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis f, Matrix.trace]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
  -- Steps 6–7: `p_{T⊥}` is self-adjoint, and `p_{T⊥} q(eᵢ, 0) = 0` as `p_T q(eᵢ, 0) = q(eᵢ, 0)`
  have hterm_cast : ∀ i : Fin n, inner ℝ (b (Fin.castAdd ℓ i))
      ((rotatedPlane q)ᗮ.starProjection (S.starProjection (b (Fin.castAdd ℓ i)))) = 0 := by
    intro i
    rw [← Submodule.inner_starProjection_left_eq_right, hb, hcast,
      Submodule.starProjection_orthogonal_val, hproj, sub_self, inner_zero_left]
  -- Step 8: `p_{T⊥} e'_j = e'_j − q(0, 0) = e'_j` and `⟨e'_j, p_S e'_j⟩ = |p_S e'_j|²`
  have hterm_nat : ∀ j : Fin ℓ, inner ℝ (b (Fin.natAdd n j))
      ((rotatedPlane q)ᗮ.starProjection (S.starProjection (b (Fin.natAdd n j)))) =
        ‖S.starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ ^ 2 := by
    intro j
    rw [← Submodule.inner_starProjection_left_eq_right, hb, hnat,
      Submodule.starProjection_orthogonal_val, hproj, hzero, map_zero, sub_zero,
      ← real_inner_self_eq_norm_sq, S.inner_starProjection_left_eq_right,
      S.starProjection_eq_self_iff.2 (S.starProjection_apply_mem _)]
  -- Step 10: `trace(p_{T⊥} ∘ p_S) = ½ |p_S − p_T|²`, since `dim S = n = dim T`
  have htr := (Submission.hsNorm_starProjection_trace_identities).2.2 (n + ℓ) S (rotatedPlane q)
    (by rw [hS, hdimT])
  -- Steps 9 and 11: split the trace over the indices `castAdd ℓ i` and `natAdd n j`
  rw [← htr, htrace, Fin.sum_univ_add]
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [Finset.sum_eq_zero fun i _ => hterm_cast i, zero_add]
  exact (Finset.sum_congr rfl fun j _ => hterm_nat j).symm

/-- Graph orthogonality behind Simon Ch. 5, Theorem 4.5 (p. 116), proof step (7):
`e_{n+j} − (∇f^j, 0)` is normal to the graph.  If `r` is the `j`-th row of `D`
(`⟨r, v⟩ = (D v)_j` for all `v`), then `q(0, e_j) − q(r, 0) = q(−r, e_j)` and
`⟨(−r, e_j), (v, D v)⟩ = −⟨r, v⟩ + (D v)_j = 0`, so this difference is orthogonal to every generator
`q(v, D v)` of `S`, hence lies in `Sᗮ`, and the orthogonal projection onto `S` takes the same value
at `q(0, e_j)` and at `q(r, 0)`. -/
theorem gwe_gta_graph_row_orthogonal : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (D : Rn n →L[ℝ] Rn ℓ) (j : Fin ℓ) (r : Rn n), (∀ v : Rn n, inner ℝ r v = D v j) → (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))) = (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint r 0)) := by
  have hGA := any_radius_gr_la_graphPoint_algebra
  intro n ℓ q D j r hr
  -- the difference `q(0, e_j) − q(r, 0) = q(0 − r, e_j − 0)`, by linearity of `q` and (L2)
  have hdiff : q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))) - q (graphPoint r 0) =
      q (graphPoint (0 - r) (EuclideanSpace.single j (1 : ℝ) - 0)) := by
    rw [← map_sub, (hGA n ℓ).2.2.2.1]
  -- it is orthogonal to every generator `q(v, D v)`: by (IP), `⟪·, ·⟫ = −⟪r, v⟫ + (D v)_j = 0`
  have hgen : ∀ v : Rn n, inner ℝ (q (graphPoint (0 - r) (EuclideanSpace.single j (1 : ℝ) - 0)))
      (q (graphPoint v (D v))) = 0 := by
    intro v
    rw [LinearIsometryEquiv.inner_map_map, (hGA n ℓ).2.2.2.2.2.2, zero_sub, sub_zero,
      inner_neg_left, hr v, EuclideanSpace.inner_single_left]
    simp
  -- hence it lies in `Sᗮ`: the span `S` of the generators lies in `(ℝ ∙ x)ᗮ`
  have hmem : q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))) - q (graphPoint r 0) ∈
      (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v))))ᗮ := by
    rw [hdiff]
    have hle : Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v))) ≤
        (ℝ ∙ q (graphPoint (0 - r) (EuclideanSpace.single j (1 : ℝ) - 0)))ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨v, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hgen v)
    refine (Submodule.mem_orthogonal' _ _).mpr (fun u hu => ?_)
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hu)
  -- the orthogonal projection onto `S` vanishes on `Sᗮ`
  have h0 := (Submodule.starProjection_apply_eq_zero_iff _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0
/-- Rows of a linear map `D : ℝⁿ → ℝ^ℓ` (in the proof of Simon Ch. 5, Theorem 4.5, `D = Df(x)`,
whose rows are the gradients `∇f^j`): (i) every row `r` of `D`, i.e. `⟪r, v⟫ = (D v)_j` for all `v`,
has `|r| ≤ ‖D‖`; (ii) the rows `R_j` (Riesz representatives of `v ↦ (D v)_j`) satisfy
`Σ_j |R_j|² = |D|²`. -/
theorem gwe_gta_row_bounds : ∀ (n ℓ : ℕ) (D : Rn n →L[ℝ] Rn ℓ), (∀ (j : Fin ℓ) (r : Rn n), (∀ v : Rn n, inner ℝ r v = D v j) → ‖r‖ ≤ ‖D‖) ∧ ∃ R : Fin ℓ → Rn n, (∀ (j : Fin ℓ) (v : Rn n), inner ℝ (R j) v = D v j) ∧ ∑ j : Fin ℓ, ‖R j‖ ^ 2 = hsNormSq D := by
  intro n ℓ D
  refine ⟨?_, ?_⟩
  · -- (i) `|r|² = ⟪r, r⟫ = (D r)_j ≤ |D r| ≤ ‖D‖ |r|`; divide by `|r|` unless `r = 0`.
    intro j r hr
    have h1 : ‖r‖ ^ 2 ≤ ‖D‖ * ‖r‖ :=
      calc ‖r‖ ^ 2 = inner ℝ r r := (real_inner_self_eq_norm_sq r).symm
        _ = D r j := hr r
        _ ≤ |D r j| := le_abs_self _
        _ = ‖D r j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖D r‖ := PiLp.norm_apply_le (D r) j
        _ ≤ ‖D‖ * ‖r‖ := D.le_opNorm r
    rcases (norm_nonneg r).eq_or_lt with h | h
    · rw [← h]
      exact norm_nonneg D
    · nlinarith
  · -- (ii) `R_j` is the Riesz representative of `v ↦ (D v)_j`; its coordinates are `(D eᵢ)_j`.
    let R : Fin ℓ → Rn n := fun j =>
      (InnerProductSpace.toDual ℝ (Rn n)).symm ((EuclideanSpace.proj j).comp D)
    have hR : ∀ (j : Fin ℓ) (v : Rn n), inner ℝ (R j) v = D v j := by
      intro j v
      simp only [R, InnerProductSpace.toDual_symm_apply]
      rfl
    refine ⟨R, hR, ?_⟩
    have hcoord : ∀ (j : Fin ℓ) (i : Fin n), R j i = D (EuclideanSpace.single i 1) j := by
      intro j i
      rw [← hR j (EuclideanSpace.single i 1), EuclideanSpace.inner_single_right]
      simp
    -- Parseval in `ℝⁿ` and in `ℝ^ℓ`, after exchanging the two finite sums.
    unfold hsNormSq
    calc ∑ j : Fin ℓ, ‖R j‖ ^ 2
        = ∑ j : Fin ℓ, ∑ i : Fin n, (D (EuclideanSpace.single i 1) j) ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [EuclideanSpace.real_norm_sq_eq]
          exact Finset.sum_congr rfl fun i _ => by rw [hcoord]
      _ = ∑ i : Fin n, ∑ j : Fin ℓ, (D (EuclideanSpace.single i 1) j) ^ 2 := Finset.sum_comm
      _ = ∑ i : Fin n, ‖D (EuclideanSpace.single i 1)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [EuclideanSpace.real_norm_sq_eq]
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
/-- Simon Ch. 5, 2.4, steps 1–2 of the two-sided mass bounds, with `ω > 0` and `κ > 0` arbitrary:
for `C = max(1, C₊, C₋)` and `δP = min(1/8, κ, 1/(2C))`, where `A = 1 + n 2ⁿ⁺⁴`,
`C₊ = A + (9e²2ⁿ/4 + 2e/ω)/κ` and `C₋ = (1 + 1/ω)/κ`, every `t ∈ (0, δP]` satisfies, with
`Λ = t/κ`, `e^{2Λ} ((1 + t)/(1 − 4t)ⁿ) ω + 2e^{Λ} Λ ≤ (1 + C t) ω` and
`(1 − C t) ω ≤ e^{−Λ} (ω − Λ)` (convexity of `exp`, `1 − Λ ≤ e^{−Λ}` and Bernoulli). -/
theorem ted_adb_constants : ∀ (n : ℕ) (κ ω : ℝ), 0 < κ → 0 < ω → ∃ C δP : ℝ, 1 ≤ C ∧ 0 < δP ∧ δP ≤ 1 / 8 ∧ δP ≤ κ ∧ C * δP ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → t ≤ δP → Real.exp (2 * (t / κ)) * ((1 + t) / (1 - 4 * t) ^ n * ω) + 2 * Real.exp (t / κ) * (t / κ) ≤ (1 + C * t) * ω ∧ (1 - C * t) * ω ≤ Real.exp (-(t / κ)) * (ω - t / κ) := by
  intro n κ ω hκ hω
  -- Step 1: the constants `e`, `A`, `C₊`, `C₋` and `C = max(1, C₊, C₋)`.
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = Real.exp 1 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 + (n : ℝ) * 2 ^ (n + 4) := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ : ∃ Cp : ℝ, Cp = A + (9 * e ^ 2 * 2 ^ n / 4 + 2 * e / ω) / κ := ⟨_, rfl⟩
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = (1 + 1 / ω) / κ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max 1 (max Cp Cm) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := hC ▸ le_max_left _ _
  have hCpC : Cp ≤ C := hC ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hCmC : Cm ≤ C := hC ▸ (le_max_right _ _).trans (le_max_right _ _)
  have hC0 : 0 < C := one_pos.trans_le hC1
  -- Step 2: `δP = min(1/8, κ, 1/(2C))` satisfies the side conditions.
  refine ⟨C, min (1 / 8) (min κ (1 / (2 * C))), hC1,
    lt_min (by norm_num) (lt_min hκ (by positivity)), min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _), ?_, ?_⟩
  · calc C * min (1 / 8) (min κ (1 / (2 * C))) ≤ C * (1 / (2 * C)) :=
          mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) hC0.le
      _ = 1 / 2 := by field_simp
  intro t ht htδ
  -- Step 3: `t ≤ 1/8` (so `1 − 4t ≥ 1/2`), `Λ = t/κ ∈ (0, 1]` and `q = (1 − 4t)ⁿ > 0`.
  have ht8 : t ≤ 1 / 8 := htδ.trans (min_le_left _ _)
  have htκ : t ≤ κ := htδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = t / κ := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (1 - 4 * t) ^ n := ⟨_, rfl⟩
  rw [← hΛ, ← hq]
  have hΛ0 : 0 < Λ := hΛ ▸ div_pos ht hκ
  have hΛ1 : Λ ≤ 1 := hΛ ▸ (div_le_one hκ).2 htκ
  have hq0 : 0 < q := hq ▸ pow_pos (by linarith) n
  -- Step 4 (E1): `e^{2Λ} ≤ 1 + 2e²Λ` (convexity of `exp`), `e^{Λ} ≤ e` and `1 − Λ ≤ e^{−Λ} ≤ 1`.
  have hexp2 : Real.exp (2 * Λ) ≤ 1 + 2 * e ^ 2 * Λ := by
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (2 : ℝ))
      (sub_nonneg.2 hΛ1) hΛ0.le (sub_add_cancel 1 Λ)
    have he2 : Real.exp 2 = e ^ 2 := by rw [he, sq, ← Real.exp_add]; norm_num
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, he2] at h
    rw [mul_comm Λ 2] at h
    linarith [mul_nonneg hΛ0.le (sq_nonneg e)]
  have hexp1 : Real.exp Λ ≤ e := he ▸ Real.exp_le_exp.2 hΛ1
  have hexpm : 1 - Λ ≤ Real.exp (-Λ) := Real.one_sub_le_exp_neg Λ
  have hexpm1 : Real.exp (-Λ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  -- Step 5 (E2): Bernoulli gives `q ≥ 1 − 4nt`; also `2ⁿ q = (2(1 − 4t))ⁿ ≥ 1`.
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbern : 1 - 4 * n * t ≤ q := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -4 * t by linarith) n
    calc 1 - 4 * n * t = 1 + n * (-4 * t) := by ring
      _ ≤ (1 + -4 * t) ^ n := h
      _ = q := by rw [hq]; ring
  have h2q : 1 ≤ 2 ^ n * q := by
    rw [hq, ← mul_pow]
    exact one_le_pow₀ (by linarith)
  -- `(1 + t)/q ≤ 1 + A t`, as `(1 + A t) q = (1 + t) q + 16nt (2ⁿ q) ≥ (1 + t)(1 − 4nt) + 16nt`.
  have ha1 : (1 + t) / q ≤ 1 + A * t := by
    rw [div_le_iff₀ hq0]
    have hAt : A * t = t + 16 * n * t * 2 ^ n := by rw [hA, pow_add]; ring
    calc 1 + t ≤ (1 + t) * (1 - 4 * n * t) + 16 * n * t := by
          linarith [mul_nonneg (mul_nonneg hn0 ht.le) (by linarith : (0 : ℝ) ≤ 3 - t)]
      _ ≤ (1 + t) * q + 16 * n * t * (2 ^ n * q) :=
          add_le_add (mul_le_mul_of_nonneg_left hbern (by linarith))
            (le_mul_of_one_le_right (by positivity) h2q)
      _ = (1 + A * t) * q := by rw [hAt]; ring
  -- `(1 + t)/q ≤ (9/8) 2ⁿ`, as `1 + t ≤ 9/8 ≤ (9/8) 2ⁿ q`.
  have ha2 : (1 + t) / q ≤ 9 / 8 * 2 ^ n := by
    rw [div_le_iff₀ hq0]
    linarith
  have hB0 : 0 ≤ (1 + t) / q * ω := by positivity
  constructor
  · -- Step 6 (P): the left side is at most `(1 + C₊ t) ω ≤ (1 + C t) ω`.
    have hP1 : Real.exp (2 * Λ) * ((1 + t) / q * ω) ≤
        (1 + t) / q * ω + 2 * e ^ 2 * Λ * ((1 + t) / q * ω) := by
      linarith [mul_le_mul_of_nonneg_right hexp2 hB0]
    have hP2 : (1 + t) / q * ω ≤ (1 + A * t) * ω := mul_le_mul_of_nonneg_right ha1 hω.le
    have hP3 : 2 * e ^ 2 * Λ * ((1 + t) / q * ω) ≤ 2 * e ^ 2 * Λ * (9 / 8 * 2 ^ n * ω) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha2 hω.le) (by positivity)
    have hP4 : 2 * Real.exp Λ * Λ ≤ 2 * e * Λ := by
      linarith [mul_le_mul_of_nonneg_right hexp1 hΛ0.le]
    have hP5 : (1 + A * t) * ω + 2 * e ^ 2 * Λ * (9 / 8 * 2 ^ n * ω) + 2 * e * Λ =
        (1 + Cp * t) * ω := by
      rw [hCp, hΛ]
      field_simp
      ring
    have hP6 : (1 + Cp * t) * ω ≤ (1 + C * t) * ω :=
      mul_le_mul_of_nonneg_right (by linarith [mul_le_mul_of_nonneg_right hCpC ht.le]) hω.le
    linarith
  · -- Step 7 (M): `(1 − C t) ω ≤ (1 − C₋ t) ω = ω − Λ − Λω ≤ e^{−Λ} (ω − Λ)`.
    have hM1 : (1 - C * t) * ω ≤ ω - Λ - Λ * ω := by
      have hCmt : Cm * t * ω = Λ + Λ * ω := by
        rw [hCm, hΛ]
        field_simp
        ring
      linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCmC ht.le) hω.le]
    rcases le_or_gt 0 (ω - Λ) with h | h
    · linarith [mul_le_mul_of_nonneg_right hexpm h, sq_nonneg Λ]
    · linarith [mul_le_mul_of_nonpos_right hexpm1 h.le, mul_pos hΛ0 hω]
/-- Simon Ch. 5, hypotheses 2.3 restricted to a sub-ball `B_r(z) ⊆ B_ρ(0)` with `0 < r ≤ ρ`:
`B_r(z) ⊆ U`, `∫_{B_r(z)} |H|ᵖ dμ_V < ∞`, `(r^{p−n} ∫_{B_r(z)} |H|ᵖ dμ_V)^{1/p} ≤ δ` and
`μ_V(B_r(z)) ≤ (1 + δ) ω_n ρⁿ`.  Since `p > n ≥ 0`, both exponents `p − n` and `1/p` are positive,
so the scaled `Lᵖ` norm is monotone under shrinking the ball, and its finiteness on `B_ρ(0)` with
`ρ^{p−n} > 0` forces `∫_{B_ρ(0)} |H|ᵖ dμ_V < ∞`. -/
theorem aal_allard_subball_bounds : ∀ (n ℓ : ℕ) (p : ℝ), (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), V.AllardHypotheses H p δ ρ → ∀ (z : Amb n ℓ) (r : ℝ), 0 < r → r ≤ ρ → closedBall z r ⊆ closedBall 0 ρ → closedBall z r ⊆ U ∧ ∫⁻ x in closedBall z r, ‖H x‖ₑ ^ p ∂V.weight < ⊤ ∧ V.scaledLpNorm H p z r ≤ ENNReal.ofReal δ ∧ V.weight (closedBall z r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * ρ ^ n)) := by
  intro n ℓ p hp U V H δ ρ hA z r hr hrρ hball
  obtain ⟨hρ, -, -, -, hU, hmass, hK⟩ := hA
  -- `p > n ≥ 0`, so `p - n > 0` and `1 / p > 0`.
  have hpn : 0 < p - n := sub_pos.mpr hp
  have hp' : 0 < 1 / p := one_div_pos.mpr ((Nat.cast_nonneg n).trans_lt hp)
  -- `I(z, r) ≤ I(0, ρ)` by monotonicity of the lower integral in the domain.
  have hI : ∫⁻ x in closedBall z r, ‖H x‖ₑ ^ p ∂V.weight ≤
      ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight := lintegral_mono_set hball
  -- `K(0, ρ) = (ρ^{p−n} I(0, ρ))^{1/p} ≤ δ < ∞` forces `ρ^{p−n} I(0, ρ) < ∞`.
  have hK' : (ENNReal.ofReal (ρ ^ (p - n)) *
      ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) ≤ ENNReal.ofReal δ := hK
  have hfin : ENNReal.ofReal (ρ ^ (p - n)) *
      ∫⁻ x in closedBall 0 ρ, ‖H x‖ₑ ^ p ∂V.weight < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos hp').mp (hK'.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hball.trans hU, ?_, ?_, (measure_mono hball).trans hmass⟩
  · -- Since `ρ^{p−n} > 0`, `I(0, ρ) < ∞`, hence `I(z, r) < ∞`.
    exact hI.trans_lt (ENNReal.lt_top_of_mul_ne_top_right hfin.ne
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ _)).ne')
  · -- `r^{p−n} ≤ ρ^{p−n}` and `I(z, r) ≤ I(0, ρ)` give `K(z, r) ≤ K(0, ρ) ≤ δ`.
    refine le_trans ?_ hK'
    exact ENNReal.rpow_le_rpow (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow hr.le hrρ hpn.le)) hI) hp'.le
/-- Simon Ch. 5, 2.4, step (5.1) of the lower density bound, abstracted: put
`Φ(u) = F(u) (m(u)/uⁿ) + (F(u) − 1)`.  If `|F(u) − 1| ≤ Λ (u/R)^α` on `(0, R]` with `α > 0`, `Φ` is
nondecreasing on `(0, R]`, and for every `ε > 0` eventually `(1 − ε) ω uⁿ ≤ m(u)` as `u ↓ 0`, then
`ω ≤ Φ(t)` for every `t ∈ (0, R]` (let `u ↓ 0` in `Φ(u) ≤ Φ(t)`, using `F(u) → 1`). -/
theorem aal_monotone_quantity_ge_density : ∀ (n : ℕ) (α ω R Λ : ℝ) (m F : ℝ → ℝ), 0 < α → 0 < ω → 0 < R → (∀ u : ℝ, 0 < u → u ≤ R → |F u - 1| ≤ Λ * (u / R) ^ α) → (∀ u t : ℝ, 0 < u → u ≤ t → t ≤ R → F u * (m u / u ^ n) + (F u - 1) ≤ F t * (m t / t ^ n) + (F t - 1)) → (∀ ε : ℝ, 0 < ε → ∀ᶠ u in 𝓝[>] (0 : ℝ), (1 - ε) * (ω * u ^ n) ≤ m u) → ∀ t : ℝ, 0 < t → t ≤ R → ω ≤ F t * (m t / t ^ n) + (F t - 1) := by
  intro n α ω R Λ m F hα hω hR hF hmono hlow t ht htR
  -- `Λ (u/R)^α → 0` as `u → 0+`, since `x ↦ x^α` is continuous at `0` with `0^α = 0` (`α > 0`).
  have hlim : Tendsto (fun u : ℝ => Λ * (u / R) ^ α) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun u : ℝ => Λ * (u / R) ^ α) 0 :=
      continuousAt_const.mul ((continuousAt_id.div_const R).rpow_const (Or.inr hα.le))
    have h := hc.tendsto
    simp only [zero_div, Real.zero_rpow hα.ne', mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- Suppose `Φ(t) < ω` and pick `η ∈ (0, 1/2]` with `η (2ω + 1) ≤ (ω − Φ(t))/2`.
  refine not_lt.mp fun hcon => ?_
  obtain ⟨η, hη0, hη2, hηd⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧
      η * (2 * (2 * ω + 1)) ≤ ω - (F t * (m t / t ^ n) + (F t - 1)) := by
    refine ⟨min (1 / 2) ((ω - (F t * (m t / t ^ n) + (F t - 1))) / (2 * (2 * ω + 1))),
      lt_min (by norm_num) (div_pos (sub_pos.mpr hcon) (by positivity)), min_le_left _ _, ?_⟩
    rw [← le_div_iff₀ (by positivity)]
    exact min_le_right _ _
  -- A small radius `u ∈ (0, t)` with `Λ (u/R)^α < η` and `(1 − η) ω uⁿ ≤ m(u)`.
  have hsmall : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 t := Ioo_mem_nhdsGT ht
  obtain ⟨u, ⟨hu0, hut⟩, huΛ, hum⟩ :=
    (hsmall.and ((hlim.eventually (gt_mem_nhds hη0)).and (hlow η hη0))).exists
  -- `|F(u) − 1| < η`, so `F(u) > 1 − η ≥ 1/2`.
  have hFu : 1 - η < F u := by
    have h := (abs_lt.mp ((hF u hu0 (hut.le.trans htR)).trans_lt huΛ)).1
    linarith
  -- `m(u)/uⁿ ≥ (1 − η) ω ≥ 0`, hence `F(u) (m(u)/uⁿ) ≥ (1 − η)² ω`.
  have hmu : (1 - η) * ω ≤ m u / u ^ n := by
    rw [le_div_iff₀ (pow_pos hu0 n)]
    linarith
  have hprod : (1 - η) * ((1 - η) * ω) ≤ F u * (m u / u ^ n) :=
    mul_le_mul hFu.le hmu (mul_nonneg (by linarith) hω.le) (by linarith)
  -- `Φ(u) ≥ (1 − η)² ω − η ≥ ω − η (2ω + 1) > Φ(t)`, contradicting `Φ(u) ≤ Φ(t)`.
  have hmon := hmono u t hu0 hut.le htR
  linarith [mul_nonneg (sq_nonneg η) hω.le]
/-- Simon Ch. 4, 3.9–3.10 and 4.5–4.9, at one point `x` of an arbitrary measure `μ`: put
`c(s) = A (s/R)^β` with `β > 0` and `Φ(s) = F(s) s⁻ⁿ μ(B_s(x)) + (F(s) − 1)`.  If `|F − 1| ≤ c` on
`(0, R]`, `Φ` is nondecreasing on `(0, R]` and `μ(B_r(x)) / (ω rⁿ) → θ₀` as `r ↓ 0`, then
`F(s) → 1` and `Φ(s) → ω θ₀` as `s ↓ 0`, hence `ω θ₀ ≤ Φ(t) ≤ (1 + c(t)) t⁻ⁿ μ(B_t(x)) + c(t)`
for every `t ∈ (0, R]`. -/
theorem ted_dge1_density_le_monotone_bound : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (x : Amb n ℓ) (ω R A β θ₀ : ℝ) (F : ℝ → ℝ), 0 < ω → 0 < R → 0 < β → 0 ≤ θ₀ → (∀ t : ℝ, 0 < t → t ≤ R → |F t - 1| ≤ A * (t / R) ^ β) → (∀ s t : ℝ, 0 < s → s ≤ t → t ≤ R → F s * ((μ (closedBall x s)).toReal / s ^ n) + (F s - 1) ≤ F t * ((μ (closedBall x t)).toReal / t ^ n) + (F t - 1)) → Tendsto (fun r : ℝ => μ (closedBall x r) / ENNReal.ofReal (ω * r ^ n)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ₀)) → ∀ t : ℝ, 0 < t → t ≤ R → ω * θ₀ ≤ (1 + A * (t / R) ^ β) * ((μ (closedBall x t)).toReal / t ^ n) + A * (t / R) ^ β := by
  intro n ℓ μ x ω R A β θ₀ F hω hR hβ hθ₀ hF hmono hdens t ht htR
  -- Step 1: `c(s) = A (s/R)^β → A · 0^β = 0` as `s ↓ 0`, because `β > 0`.
  have hc : Tendsto (fun s : ℝ => A * (s / R) ^ β) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun s : ℝ => A * (s / R) ^ β) (𝓝 0) (𝓝 (A * ((0 : ℝ) / R) ^ β)) :=
      (((continuous_id.div_const R).tendsto 0).rpow_const (Or.inr hβ.le)).const_mul A
    rw [zero_div, Real.zero_rpow hβ.ne', mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  -- The interval `(0, t) ⊆ (0, R]` is a right neighbourhood of `0`.
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 t := Ioo_mem_nhdsGT ht
  -- Step 2: `F(s) → 1` as `s ↓ 0`, squeezing `0 ≤ |F(s) − 1| ≤ c(s)` on `(0, t)`.
  have hF1 : Tendsto F (𝓝[>] 0) (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hc
    filter_upwards [hev] with s hs
    rw [Real.norm_eq_abs]
    exact hF s hs.1 (hs.2.le.trans htR)
  -- Step 3: `s⁻ⁿ μ(B_s(x)) = ω · toReal (μ(B_s(x)) / ofReal (ω sⁿ)) → ω θ₀` as `s ↓ 0`, since
  -- `toReal` is continuous at the finite limit `ofReal θ₀`.
  have hm : Tendsto (fun s : ℝ => (μ (closedBall x s)).toReal / s ^ n) (𝓝[>] 0) (𝓝 (ω * θ₀)) := by
    have hreal : Tendsto (fun s => (μ (closedBall x s) / ENNReal.ofReal (ω * s ^ n)).toReal)
        (𝓝[>] 0) (𝓝 θ₀) := by
      have h := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hdens
      rwa [ENNReal.toReal_ofReal hθ₀] at h
    have heq : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        ω * (μ (closedBall x s) / ENNReal.ofReal (ω * s ^ n)).toReal =
          (μ (closedBall x s)).toReal / s ^ n := by
      filter_upwards [hev] with s hs
      have hsn : 0 < s ^ n := pow_pos hs.1 n
      rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity)]
      field_simp
    exact (hreal.const_mul ω).congr' heq
  -- Step 4: `Φ(s) → 1 · (ω θ₀) + (1 − 1) = ω θ₀` as `s ↓ 0`.
  have hΦ : Tendsto (fun s => F s * ((μ (closedBall x s)).toReal / s ^ n) + (F s - 1)) (𝓝[>] 0)
      (𝓝 (ω * θ₀)) := by
    simpa using (hF1.mul hm).add (hF1.sub_const 1)
  -- Step 5: `ω θ₀ ≤ Φ(t)`, letting `s ↓ 0` in `Φ(s) ≤ Φ(t)`, `s ∈ (0, t)`.
  have hle : ω * θ₀ ≤ F t * ((μ (closedBall x t)).toReal / t ^ n) + (F t - 1) := by
    refine le_of_tendsto hΦ ?_
    filter_upwards [hev] with s hs
    exact hmono s t hs.1 hs.2.le htR
  -- Step 6: `F(t) − 1 ≤ c(t)` and `t⁻ⁿ μ(B_t(x)) ≥ 0` give
  -- `Φ(t) ≤ (1 + c(t)) t⁻ⁿ μ(B_t(x)) + c(t)`.
  have hFt : F t - 1 ≤ A * (t / R) ^ β := (le_abs_self _).trans (hF t ht htR)
  have hmt : 0 ≤ (μ (closedBall x t)).toReal / t ^ n :=
    div_nonneg ENNReal.toReal_nonneg (pow_pos ht n).le
  have hmul := mul_le_mul_of_nonneg_right (show F t ≤ 1 + A * (t / R) ^ β by linarith) hmt
  linarith
/-- Simon Ch. 4, 3.11 and Remark 4.10(1), for an arbitrary measure `μ`: let `y ∈ spt μ` with
`μ(B_{2r}(y)) < ∞`, let `c ≥ 0` on `(0, r]` with `c(t) → 0` as `t ↓ 0`, and suppose that for
`μ`-a.e. `x ∈ B̆_r(y)` the estimate `ω ≤ (1 + c(t)) t⁻ⁿ μ(B_t(x)) + c(t)` holds for every
`t ∈ (0, r]`.  Every neighbourhood of `y` has positive measure, so it contains such a good point
`x`; `B_t(x) ⊆ B_u(y)` when `|x − y| < u − t`, and `μ(B_u(y)) → μ(B_t(y))` as `u ↓ t`, so the
estimate also holds at `y`.  Since `c(s) → 0`, this gives `μ(B_s(y)) ≥ (1 − ε) ω sⁿ` for all small
`s > 0`. -/
theorem ted_dge1_support_density_lower_bound : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (ω r : ℝ) (c : ℝ → ℝ), 0 < ω → 0 < r → y ∈ μ.support → μ (closedBall y (2 * r)) < ⊤ → (∀ t : ℝ, 0 < t → t ≤ r → 0 ≤ c t) → Tendsto c (𝓝[>] 0) (𝓝 0) → (∀ᵐ x ∂μ, x ∈ ball y r → ∀ t : ℝ, 0 < t → t ≤ r → ω ≤ (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) + c t) → ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((1 - ε) * (ω * s ^ n)) ≤ μ (closedBall y s) := by
  intro n ℓ μ y ω r c hω hr hy hfin hc0 hc hae ε hε
  -- Step 1: `μ(B_u(y)) ≤ μ(B_{2r}(y)) < ∞` for `u ≤ 2r`.
  have hfin' : ∀ u : ℝ, u ≤ 2 * r → μ (closedBall y u) ≠ ⊤ := fun u hu =>
    (lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall hu)) hfin).ne
  -- Steps 2–4: the estimate also holds at `y`, for every `t ∈ (0, r]`.
  have hA : ∀ t : ℝ, 0 < t → t ≤ r →
      ω ≤ (1 + c t) * ((μ (closedBall y t)).toReal / t ^ n) + c t := by
    intro t ht htr
    have hct : 0 ≤ c t := hc0 t ht htr
    have htn : 0 < t ^ n := pow_pos ht n
    -- Steps 2–3: for `u ∈ (t, t + r)`, `B̆_{u−t}(y)` has positive measure, so it is not inside the
    -- null set of bad points; a good point `x` in it has `B_t(x) ⊆ B_u(y)`.
    have hu : ∀ u : ℝ, t < u → u < t + r →
        ω ≤ (1 + c t) * ((μ (closedBall y u)).toReal / t ^ n) + c t := by
      intro u htu hut
      have hη : 0 < u - t := sub_pos.mpr htu
      have hpos : 0 < μ (ball y (u - t)) :=
        (Measure.mem_support_iff_forall y).mp hy _ (ball_mem_nhds y hη)
      obtain ⟨x, hxb, hx⟩ : ∃ x ∈ ball y (u - t), (x ∈ ball y r → ∀ t : ℝ, 0 < t → t ≤ r →
          ω ≤ (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) + c t) := by
        by_contra hcon
        have hsub : ball y (u - t) ⊆ {x | ¬ (x ∈ ball y r → ∀ t : ℝ, 0 < t → t ≤ r →
            ω ≤ (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) + c t)} := by
          intro x hx hgood
          exact hcon ⟨x, hx, hgood⟩
        exact absurd (measure_mono_null hsub (ae_iff.mp hae)) hpos.ne'
      have hxr : x ∈ ball y r := ball_subset_ball (by linarith) hxb
      have h1 := hx hxr t ht htr
      have hsub : closedBall x t ⊆ closedBall y u := by
        intro z hz
        rw [mem_closedBall] at hz ⊢
        rw [mem_ball] at hxb
        linarith [dist_triangle z x y]
      have hle : (μ (closedBall x t)).toReal ≤ (μ (closedBall y u)).toReal :=
        ENNReal.toReal_mono (hfin' u (by linarith)) (measure_mono hsub)
      have : (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) ≤
          (1 + c t) * ((μ (closedBall y u)).toReal / t ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact div_le_div_of_nonneg_right hle htn.le
      linarith
    -- Step 4: `μ(B_u(y)) → μ(B_t(y))` as `u ↓ t`, by continuity from above
    -- (`⋂_{u > t} B_u(y) = B_t(y)` and `μ(B_{2r}(y)) < ∞`); pass to the limit in Step 3.
    have hlim : Tendsto (fun u => (μ (closedBall y u)).toReal) (𝓝[>] t)
        (𝓝 ((μ (closedBall y t)).toReal)) := by
      have h1 := tendsto_measure_biInter_gt (μ := μ) (s := fun u => closedBall y u) (a := t)
        (fun u _ => measurableSet_closedBall.nullMeasurableSet)
        (fun i j _ hij => closedBall_subset_closedBall hij)
        ⟨2 * r, by linarith, hfin.ne⟩
      rw [biInter_gt_closedBall] at h1
      exact (ENNReal.tendsto_toReal (hfin' t (by linarith))).comp h1
    have hlim2 : Tendsto (fun u => (1 + c t) * ((μ (closedBall y u)).toReal / t ^ n) + c t)
        (𝓝[>] t) (𝓝 ((1 + c t) * ((μ (closedBall y t)).toReal / t ^ n) + c t)) :=
      ((hlim.div_const _).const_mul _).add_const _
    apply ge_of_tendsto hlim2
    filter_upwards [Ioo_mem_nhdsGT (by linarith : t < t + r)] with u hu'
    exact hu u hu'.1 hu'.2
  rcases le_or_gt 1 ε with h1 | h1
  -- Step 5: for `ε ≥ 1` the left side is `ofReal` of a nonpositive number, i.e. `0`.
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : (0:ℝ) < s := hs
    have : (1 - ε) * (ω * s ^ n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [ENNReal.ofReal_of_nonpos this]
    exact zero_le
  -- Step 6: for `0 < ε < 1` put `γ = εω/(1 + ω)`.  Once `c(s) < γ` and `s < r`, the estimate at `y`
  -- gives `ω ≤ (1 + γ) q + γ` for `q = s⁻ⁿ μ(B_s(y))`, which forces `q ≥ (1 − ε) ω`.
  · set γ := ε * ω / (1 + ω) with hγ_def
    have hγ : 0 < γ := by positivity
    have hγ' : γ * (1 + ω) = ε * ω := by rw [hγ_def]; field_simp
    have hev1 : ∀ᶠ s in 𝓝[>] (0:ℝ), c s < γ := hc.eventually (gt_mem_nhds hγ)
    have hev2 : ∀ᶠ s in 𝓝[>] (0:ℝ), s ∈ Ioo 0 r := Ioo_mem_nhdsGT hr
    filter_upwards [hev1, hev2] with s hcs hs
    have hA' := hA s hs.1 hs.2.le
    have hsn : 0 < s ^ n := pow_pos hs.1 n
    have hcs0 : 0 ≤ c s := hc0 s hs.1 hs.2.le
    set q := (μ (closedBall y s)).toReal / s ^ n with hq_def
    have hq : 0 ≤ q := div_nonneg ENNReal.toReal_nonneg hsn.le
    have h2 : ω ≤ (1 + γ) * q + γ := by nlinarith
    have key : (1 - ε) * ω ≤ q := by
      by_contra hlt
      push Not at hlt
      have h3 : (1 + γ) * q < (1 + γ) * ((1 - ε) * ω) := mul_lt_mul_of_pos_left hlt (by linarith)
      have h4 : 0 < γ * ε * ω := by positivity
      nlinarith [hγ']
    have key2 : (1 - ε) * (ω * s ^ n) ≤ (μ (closedBall y s)).toReal := by
      have h5 : (μ (closedBall y s)).toReal = q * s ^ n := by
        rw [hq_def, div_mul_cancel₀ _ hsn.ne']
      rw [h5]
      nlinarith [mul_le_mul_of_nonneg_right key hsn.le]
    rw [← ENNReal.ofReal_toReal (hfin' s (by linarith [hs.2]))]
    exact ENNReal.ofReal_le_ofReal key2
/-- **Simon Ch. 4, 3.2–3.3 and 4.1** (first variation of the radial cutoff fields).  Let `V` have
generalized mean curvature `H` in `U`, with `p_{T_x M}` the projection onto an `n`-plane for
`μ_V`-a.e. `x`.  Let `φ ∈ C¹(ℝ)` with `φ = 1` on `(-∞, 1]` and `φ = 0` on `[T, ∞)`, let `ρ > 0`, and
let `B_{Tρ}(y) ⊆ U`.  Then `X(x) = φ(r/ρ)(x − y)`, `r = |x − y|`, is admissible in 3.14, and
`div_M X = n φ(r/ρ) + (r/ρ) φ'(r/ρ)(1 − |(x − y) − p_{T_x M}(x − y)|²/r²)` `μ_V`-a.e.
(both sides equal `n` at `x = y`).  So `∫ div_M X dμ_V = −∫ X · H dμ_V` is the stated identity. -/
theorem aal_radial_first_variation_identity : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (y : Amb n ℓ) (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → closedBall y (T * ρ) ⊆ U → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) * (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) ∂V.weight = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
  intro n ℓ U V H hH hP y φ T ρ hφ hφ1 hφT hρ hU
  -- Step 1: the field `X(x) = φ(|x - y|/ρ)(x - y)` is `C¹`.  On `B̆_ρ(y)` it is `x - y`.
  obtain ⟨X, hX⟩ : ∃ X : Amb n ℓ → Amb n ℓ, X = fun x => φ (‖x - y‖ / ρ) • (x - y) := ⟨_, rfl⟩
  have hXball : ∀ x ∈ ball y ρ, X =ᶠ[𝓝 x] fun z => z - y := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    have : ‖z - y‖ / ρ ≤ 1 := by
      rw [mem_ball, dist_eq_norm] at hz
      rw [div_le_one hρ]; exact hz.le
    simp [hX, hφ1 _ this]
  have hXcd : ContDiff ℝ 1 X := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxy : x = y
    · exact (contDiffAt_id.sub contDiffAt_const).congr_of_eventuallyEq
        (hXball x (by rw [hxy]; exact mem_ball_self hρ))
    · rw [hX]
      have h1 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => ‖z - y‖) x :=
        (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hxy)
      have h2 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => φ (‖z - y‖ / ρ)) x :=
        hφ.contDiffAt.comp x (h1.div_const ρ)
      exact h2.smul (contDiffAt_id.sub contDiffAt_const)
  -- Step 2: `X = 0` off `B_{Tρ}(y)`, a compact subset of `U`, so `X` is admissible in 3.14.
  have hXzero : ∀ z, T * ρ < ‖z - y‖ → X z = 0 := by
    intro z hz
    have hT : T ≤ ‖z - y‖ / ρ := by rw [le_div_iff₀ hρ]; exact hz.le
    rw [hX]; simp [hφT _ hT]
  have hsupp : tsupport X ⊆ closedBall y (T * ρ) := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    by_contra h
    rw [mem_closedBall, dist_eq_norm, not_le] at h
    exact hz (hXzero z h)
  have hXcs : HasCompactSupport X :=
    (isCompact_closedBall y (T * ρ)).of_isClosed_subset (isClosed_tsupport X) hsupp
  have key := hH.2 X hXcd hXcs (hsupp.trans hU)
  -- Step 3: `X · H = φ(r/ρ)(x - y) · H`.
  have hRHS : (fun x => inner ℝ (X x) (H x)) =
      fun x => φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) := by
    funext x; rw [hX]; exact real_inner_smul_left _ _ _
  rw [hRHS] at key
  -- Step 4: for `x ≠ y`, `DX(x) = φ(r/ρ) id + ρ⁻¹ r⁻¹ φ'(r/ρ) ((x - y) · ⬝) (x - y)`.
  have hXderiv : ∀ x, x ≠ y → HasFDerivAt X
      (φ (‖x - y‖ / ρ) • ContinuousLinearMap.id ℝ (Amb n ℓ) +
        (deriv φ (‖x - y‖ / ρ) / (ρ * ‖x - y‖)) • (innerSL ℝ (x - y)).smulRight (x - y)) x := by
    intro x hxy
    have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    -- `D|· - y|(x) = r⁻¹ (x - y) · ⬝`, from `|z - y| = √(|z - y|²)`.
    have hnorm : HasFDerivAt (fun z : Amb n ℓ => ‖z - y‖) (‖x - y‖⁻¹ • innerSL ℝ (x - y)) x := by
      have h := (Real.hasDerivAt_sqrt (pow_pos hr 2).ne').comp_hasFDerivAt x
        (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y).norm_sq
      convert h using 1
      · funext z; simp [Real.sqrt_sq (norm_nonneg _)]
      · ext v; simp [Real.sqrt_sq hr.le]; field_simp
    have hcomp : HasDerivAt (fun t => φ (t / ρ)) (deriv φ (‖x - y‖ / ρ) / ρ) ‖x - y‖ :=
      (((hφ.differentiable one_ne_zero) (‖x - y‖ / ρ)).hasDerivAt.comp ‖x - y‖
        ((hasDerivAt_id' ‖x - y‖).div_const ρ)).congr_deriv (mul_one_div _ _)
    have hc := (hcomp.comp_hasFDerivAt x hnorm).smul (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y)
    have hfun : X = ((fun t => φ (t / ρ)) ∘ fun z : Amb n ℓ => ‖z - y‖) • fun z => z - y := by
      rw [hX]; rfl
    rw [hfun]
    refine hc.congr_fderiv ?_
    ext v
    simp
    ring
  -- Step 5: `trace p_P = dim P` and `trace ((a id + c (u · ⬝) u) ∘ p_P) = a dim P + c u · p_P u`.
  have htrP : ∀ P : Submodule ℝ (Amb n ℓ),
      LinearMap.trace ℝ (Amb n ℓ) P.starProjection.toLinearMap = (Module.finrank ℝ P : ℝ) := by
    intro P
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']
    have hcomp : P.orthogonalProjectionOnto.toLinearMap.comp P.subtypeL.toLinearMap =
        LinearMap.id := by
      ext x; simp
    rw [hcomp, LinearMap.trace_id]
  have htr : ∀ (P : Submodule ℝ (Amb n ℓ)) (a c : ℝ) (u : Amb n ℓ),
      LinearMap.trace ℝ (Amb n ℓ) ((a • ContinuousLinearMap.id ℝ (Amb n ℓ) +
          c • (innerSL ℝ u).smulRight u).toLinearMap ∘ₗ P.starProjection.toLinearMap) =
        a * Module.finrank ℝ P + c * inner ℝ u (P.starProjection u) := by
    intro P a c u
    have hcomp : (a • ContinuousLinearMap.id ℝ (Amb n ℓ) +
          c • (innerSL ℝ u).smulRight u).toLinearMap ∘ₗ P.starProjection.toLinearMap =
        a • P.starProjection.toLinearMap +
          c • ((innerSL ℝ u).toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight u := by
      ext w; simp
    rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight, htrP]
    simp
  -- Step 6: `div_M X` equals the integrand at every `x` where `p_{T_x M}` projects onto an
  -- `n`-plane `P`.
  have hae : ∀ᵐ x ∂V.weight, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) *
      (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) = V.divM X x := by
    filter_upwards [hP] with x hx
    obtain ⟨P, hPn, hPx⟩ := hx
    rw [RectifiableVarifold.divM, hPx]
    by_cases hxy : x = y
    · -- At the center `DX(y) = id`, so `div_M X(y) = n = n φ(0)`.
      have hfd : fderiv ℝ X x = ContinuousLinearMap.id ℝ (Amb n ℓ) := by
        rw [(hXball x (by rw [hxy]; exact mem_ball_self hρ)).fderiv_eq]
        exact (hasFDerivAt_sub_const y).fderiv
      rw [hfd]
      simp only [ContinuousLinearMap.coe_id, LinearMap.id_comp, htrP, hPn]
      subst hxy
      simp [hφ1 0 zero_le_one]
    · -- Away from it, `(x - y) · p_P (x - y) = |p_P (x - y)|²` and Pythagoras.
      rw [(hXderiv x hxy).fderiv, htr, hPn]
      have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
      have h0 : inner ℝ ((x - y) - P.starProjection (x - y)) (P.starProjection (x - y)) = 0 :=
        Submodule.starProjection_inner_eq_zero _ _ (Submodule.starProjection_apply_mem _ _)
      have h1 : inner ℝ (x - y) (P.starProjection (x - y)) = ‖P.starProjection (x - y)‖ ^ 2 := by
        calc inner ℝ (x - y) (P.starProjection (x - y))
            = inner ℝ (((x - y) - P.starProjection (x - y)) + P.starProjection (x - y))
                (P.starProjection (x - y)) := by rw [sub_add_cancel]
          _ = ‖P.starProjection (x - y)‖ ^ 2 := by
            rw [inner_add_left, h0, zero_add, real_inner_self_eq_norm_sq]
      have h2 : ‖x - y‖ ^ 2 =
          ‖(x - y) - P.starProjection (x - y)‖ ^ 2 + ‖P.starProjection (x - y)‖ ^ 2 := by
        have := norm_add_sq_real ((x - y) - P.starProjection (x - y)) (P.starProjection (x - y))
        rw [sub_add_cancel, h0] at this
        linarith
      rw [h1]
      field_simp
      linear_combination (deriv φ (‖x - y‖ / ρ)) * h2
  -- Step 7: integrals of `μ_V`-a.e. equal functions agree.
  rw [← key]
  exact integral_congr_ae hae
/-- **Cutoff sequence** (step 4 of the proof of `ted_lpm_abstract_monotonicity`).  For `ε₁ > 0`
put `ε k = ε₁ / (k + 1)` and `φ k s = 1 - σ((s - 1) / ε k)`, where `σ = Real.smoothTransition`
is `C^∞`, monotone and `[0, 1]`-valued, with `σ = 0` on `(-∞, 0]` and `σ = 1` on `[1, ∞)`.
Then `0 < ε k ≤ ε₁` and `ε k → 0`; each `φ k` is `C¹`, antitone and `[0, 1]`-valued, with
`φ k = 1` on `(-∞, 1]` and `φ k = 0` on `[1 + ε k, ∞)`; and for `s > 1` eventually
`ε k ≤ s - 1`, so `φ k s = 0` for all large `k`. -/
theorem ted_lpm_am_cutoff_sequence : ∀ ε₁ : ℝ, 0 < ε₁ → ∃ (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), (∀ k, 0 < ε k ∧ ε k ≤ ε₁) ∧ Tendsto ε atTop (𝓝 0) ∧ (∀ k, ContDiff ℝ 1 (φ k)) ∧ (∀ k, Antitone (φ k)) ∧ (∀ k s, 0 ≤ φ k s ∧ φ k s ≤ 1) ∧ (∀ k s, s ≤ 1 → φ k s = 1) ∧ (∀ k s, 1 + ε k ≤ s → φ k s = 0) ∧ (∀ s, 1 < s → ∀ᶠ k in atTop, φ k s = 0) := by
  intro ε₁ hε₁
  -- `ε k = ε₁ / (k + 1)`, kept opaque behind its defining equation.
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun k : ℕ => ε₁ / ((k : ℝ) + 1) := ⟨_, rfl⟩
  -- Item (1): `0 < ε k ≤ ε₁`, since `1 ≤ k + 1`.
  have hεpos : ∀ k, 0 < ε k := fun k => by
    rw [hεdef]
    exact div_pos hε₁ (by positivity)
  have hεle : ∀ k, ε k ≤ ε₁ := fun k => by
    rw [hεdef]
    exact div_le_self hε₁.le (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  -- Item (2): `ε k = ε₁ * (1 / (k + 1)) → ε₁ * 0 = 0`.
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε₁
    rw [mul_zero] at h
    refine h.congr fun k => ?_
    rw [hεdef]
    ring
  -- Item (7): if `1 + ε k ≤ s` then `1 ≤ (s - 1) / ε k`, where `σ = 1`.
  have hvanish : ∀ k s, 1 + ε k ≤ s → 1 - Real.smoothTransition ((s - 1) / ε k) = 0 := by
    intro k s hs
    have h1 : 1 ≤ (s - 1) / ε k := by
      rw [le_div_iff₀ (hεpos k)]
      linarith
    rw [Real.smoothTransition.one_of_one_le h1, sub_self]
  refine ⟨fun k s => 1 - Real.smoothTransition ((s - 1) / ε k), ε,
    fun k => ⟨hεpos k, hεle k⟩, hεlim, ?_, ?_, ?_, ?_, hvanish, ?_⟩
  -- Item (3): `φ k = 1 - σ ∘ (s ↦ (s - 1) / ε k)` is `C¹`.
  · intro k
    exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
  -- Item (4): `s ≤ t` gives `(s - 1) / ε k ≤ (t - 1) / ε k`, and `σ` is monotone.
  · intro k s t hst
    have h1 : (s - 1) / ε k ≤ (t - 1) / ε k :=
      div_le_div_of_nonneg_right (by linarith) (hεpos k).le
    have h2 := Real.smoothTransition.monotone h1
    show 1 - Real.smoothTransition ((t - 1) / ε k) ≤ 1 - Real.smoothTransition ((s - 1) / ε k)
    linarith
  -- Item (5): `0 ≤ σ ≤ 1`.
  · intro k s
    have h0 := Real.smoothTransition.nonneg ((s - 1) / ε k)
    have h1 := Real.smoothTransition.le_one ((s - 1) / ε k)
    show 0 ≤ 1 - Real.smoothTransition ((s - 1) / ε k) ∧
      1 - Real.smoothTransition ((s - 1) / ε k) ≤ 1
    constructor <;> linarith
  -- Item (6): if `s ≤ 1` then `(s - 1) / ε k ≤ 0`, where `σ = 0`.
  · intro k s hs
    have h1 : (s - 1) / ε k ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (hεpos k).le
    show 1 - Real.smoothTransition ((s - 1) / ε k) = 1
    rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero]
  -- Item (8): for `s > 1`, eventually `ε k ≤ s - 1` because `ε k → 0`; then item (7) applies.
  · intro s hs
    filter_upwards [hεlim.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < s - 1))] with k hk
    exact hvanish k s (by linarith)
/-- **Coefficient bound** (step 3 of the proof of `ted_lpm_abstract_monotonicity`, with
`β = n / p`).  Put `b = I / tⁿ ≥ 0`, so `I = b tⁿ` and
`I ^ (1 - 1 / p) = b ^ (1 - 1 / p) t ^ (n (1 - 1 / p))`.  As `0 ≤ 1 - 1 / p ≤ 1`,
`b ^ (1 - 1 / p) ≤ 1 + b`, hence
`|L| ≤ K (1 + b) (t t ^ (n (1 - 1 / p))) = K t ^ (-(n / p)) (t ^ (n + 1) (1 + b))`; divide by
`t ^ (n + 1) (1 + b) > 0`. -/
theorem ted_lpm_am_coefficient_bound : ∀ (n : ℕ) (p t K I L : ℝ), 1 < p → 0 < t → 0 ≤ K → 0 ≤ I → |L| ≤ t * K * I ^ (1 - 1 / p) → |L / t ^ (n + 1) / (1 + I / t ^ n)| ≤ K * t ^ (-((n : ℝ) / p)) := by
  intro n p t K I L hp ht hK hI hL
  -- Step 4: `b ^ e ≤ 1 + b` for `b ≥ 0` and `0 ≤ e ≤ 1` (cases `b ≤ 1` and `b ≥ 1`).
  have hrpow_le : ∀ b e : ℝ, 0 ≤ b → 0 ≤ e → e ≤ 1 → b ^ e ≤ 1 + b := by
    intro b e hb he0 he1
    rcases le_total b 1 with h | h
    · have := Real.rpow_le_one hb h he0
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h he1
      rw [Real.rpow_one] at this
      linarith
  have hp0 : 0 < p := by linarith
  have htn : 0 < t ^ n := pow_pos ht n
  -- Step 2: `b = I / tⁿ ≥ 0` and `I = b tⁿ`.
  set b := I / t ^ n with hbdef
  have hb : 0 ≤ b := div_nonneg hI htn.le
  have hIb : I = b * t ^ n := by
    rw [hbdef, div_mul_cancel₀ _ htn.ne']
  -- Step 1: `0 ≤ 1 - 1 / p ≤ 1`.
  have he0 : 0 ≤ 1 - 1 / p := by
    have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
    linarith
  have he1 : 1 - 1 / p ≤ 1 := by
    have : 0 < 1 / p := by positivity
    linarith
  -- Step 3: `I ^ (1 - 1 / p) = b ^ (1 - 1 / p) t ^ (n (1 - 1 / p))`.
  have hpow : I ^ (1 - 1 / p) = b ^ (1 - 1 / p) * t ^ ((n : ℝ) * (1 - 1 / p)) := by
    rw [hIb, Real.mul_rpow hb htn.le, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  have hbe := hrpow_le b (1 - 1 / p) hb he0 he1
  have hden : 0 < 1 + b := by linarith
  -- Step 5: `|L| ≤ K (1 + b) (t t ^ (n (1 - 1 / p)))`.
  have hL' : |L| ≤ K * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := by
    calc |L| ≤ t * K * I ^ (1 - 1 / p) := hL
      _ = t * K * (b ^ (1 - 1 / p) * t ^ ((n : ℝ) * (1 - 1 / p))) := by rw [hpow]
      _ ≤ t * K * ((1 + b) * t ^ ((n : ℝ) * (1 - 1 / p))) := by
          gcongr
      _ = K * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := by ring
  -- Step 6: `t t ^ (n (1 - 1 / p)) = t ^ (-(n / p)) t ^ (n + 1)`.
  have hexp : t * t ^ ((n : ℝ) * (1 - 1 / p)) = t ^ (-((n : ℝ) / p)) * t ^ (n + 1) := by
    rw [← Real.rpow_natCast t (n + 1), ← Real.rpow_add ht]
    have h1 : t * t ^ ((n : ℝ) * (1 - 1 / p)) = t ^ ((1 : ℝ) + (n : ℝ) * (1 - 1 / p)) := by
      rw [Real.rpow_add ht, Real.rpow_one]
    rw [h1]
    congr 1
    push_cast
    field_simp
    ring
  -- Step 7: divide by `t ^ (n + 1) (1 + b) > 0`.
  rw [abs_div, abs_div, abs_of_pos (pow_pos ht (n + 1)), abs_of_pos hden, div_div,
    div_le_iff₀ (mul_pos (pow_pos ht (n + 1)) hden)]
  calc |L| ≤ K * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := hL'
    _ = K * t ^ (-((n : ℝ) / p)) * (t ^ (n + 1) * (1 + b)) := by rw [hexp]; ring
/-- Dominated convergence for radial cutoff integrals (the cutoff limit in the `Lᵖ` monotonicity
argument, Simon Ch. 4, 4.1–4.8): if `g` is `μ`-integrable on `B_S(y)`, the continuous cutoffs
`0 ≤ φ_k ≤ 1` equal `1` on `(-∞, 1]` and `0` on `[T, ∞)`, `φ_k(s) = 0` eventually for each `s > 1`,
and `T t ≤ S`, then `∫ φ_k(|x - y|/t) g dμ → ∫_{B_t(y)} g dμ`.  The integrands vanish off `B_S(y)`,
so these are integrals for `ν = μ ⌞ B_S(y)`, dominated by `|g|` and converging pointwise to
`1_{B_t(y)} g`. -/
theorem ted_lpm_am_cutoff_integral_tendsto : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (g : Amb n ℓ → ℝ) (y : Amb n ℓ) (φ : ℕ → ℝ → ℝ) (S T t : ℝ), 0 < t → 1 ≤ T → T * t ≤ S → IntegrableOn g (closedBall y S) μ → (∀ k, Continuous (φ k)) → (∀ k s, 0 ≤ φ k s ∧ φ k s ≤ 1) → (∀ k s, s ≤ 1 → φ k s = 1) → (∀ k s, T ≤ s → φ k s = 0) → (∀ s, 1 < s → ∀ᶠ k in atTop, φ k s = 0) → Tendsto (fun k => ∫ x, φ k (‖x - y‖ / t) * g x ∂μ) atTop (𝓝 (∫ x in closedBall y t, g x ∂μ)) := by
  intro n ℓ μ g y φ S T t ht hT hTt hg hφc hφ01 hφone hφ0 hφev
  -- Steps 1–2: `t ≤ T t ≤ S`, and `g` is integrable for `ν := μ ⌞ B_S(y)`.
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Amb n ℓ), ν = μ.restrict (closedBall y S) := ⟨_, rfl⟩
  have hgν : Integrable g ν := by rw [hν]; exact hg
  have htS : t ≤ S := by nlinarith
  -- Step 3: off `B_S(y)` we have `|x - y|/t ≥ T`, so every integrand vanishes there and each
  -- `μ`-integral is the corresponding `ν`-integral.
  have hout : ∀ k, ∀ x, x ∉ closedBall y S → φ k (‖x - y‖ / t) * g x = 0 := by
    intro k x hx
    have hxS : S < ‖x - y‖ := by simpa [mem_closedBall, dist_eq_norm, not_le] using hx
    have : T ≤ ‖x - y‖ / t := by
      rw [le_div_iff₀ ht]
      linarith
    rw [hφ0 k _ this, zero_mul]
  have heq : ∀ k, ∫ x, φ k (‖x - y‖ / t) * g x ∂μ = ∫ x, φ k (‖x - y‖ / t) * g x ∂ν := by
    intro k
    rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hout k x hx)]
  -- Step 4: since `B_t(y) ⊆ B_S(y)`, the limit is the `ν`-integral of `1_{B_t(y)} g`.
  have hlimeq : ∫ x in closedBall y t, g x ∂μ = ∫ x, (closedBall y t).indicator g x ∂ν := by
    rw [hν, integral_indicator measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall,
      inter_eq_left.mpr (closedBall_subset_closedBall htS)]
  rw [hlimeq]
  refine (tendsto_congr heq).mpr ?_
  -- Step 5: dominated convergence for `ν` with bound `|g|`.
  refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖) ?_ hgν.norm ?_ ?_
  · -- (a) `x ↦ φ_k(|x - y|/t)` is continuous and `g` is `ν`-a.e. strongly measurable.
    intro k
    exact ((hφc k).comp
      (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable.mul
      hgν.aestronglyMeasurable
  · -- (b) `|φ_k(|x - y|/t) g(x)| ≤ |g(x)|` since `0 ≤ φ_k ≤ 1`.
    intro k
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ01 k _).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hφ01 k _).2
  · -- (c) the sequence is constantly `g x` on `B_t(y)` and eventually `0` off it.
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ closedBall y t
    · rw [indicator_of_mem hx]
      have hle : ‖x - y‖ / t ≤ 1 := by
        rw [div_le_one ht]
        simpa [mem_closedBall, dist_eq_norm] using hx
      have : (fun k => φ k (‖x - y‖ / t) * g x) = fun _ => g x := by
        funext k
        rw [hφone k _ hle, one_mul]
      rw [this]
      exact tendsto_const_nhds
    · rw [indicator_of_notMem hx]
      have hlt : 1 < ‖x - y‖ / t := by
        rw [one_lt_div ht]
        simpa [mem_closedBall, dist_eq_norm, not_le] using hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hφev _ hlt] with k hk
      rw [hk, zero_mul]
/-- Exponential bounds for a perturbation (step 11 (a)–(d) of the abstract `Lᵖ` monotonicity
inequality, Simon Ch. 4, 4.1–4.8, used for the tilt-excess decay theorem): if `Λ > 0`, `0 ≤ q ≤ 1`
and `|u| ≤ (Λ/4) q`, then `e^{-Λ} ≤ e^u ≤ e^Λ` and `|e^u - 1| ≤ (e^{Λ/2}/2) Λ q`, and
`|e^u - 1| ≤ Λ q` if moreover `Λ ≤ 1`.  With `b = (Λ/4) q`, everything follows from the key estimate
`|e^u - 1| ≤ e^b b`, a consequence of `e^x ≥ 1 + x`. -/
theorem ted_lpm_am_exp_perturbation_bounds : ∀ (Λ q u : ℝ), 0 < Λ → 0 ≤ q → q ≤ 1 → |u| ≤ Λ / 4 * q → Real.exp (-Λ) ≤ Real.exp u ∧ Real.exp u ≤ Real.exp Λ ∧ |Real.exp u - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * q ∧ (Λ ≤ 1 → |Real.exp u - 1| ≤ Λ * q) := by
  intro Λ q u hΛ hq0 hq1 hu
  -- Step 1: `b = (Λ/4) q` lies in `[0, Λ/4]` and `-b ≤ u ≤ b`.
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = Λ / 4 * q := ⟨_, rfl⟩
  rw [← hb] at hu
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hbΛ : b ≤ Λ / 4 := by
    rw [hb]
    calc Λ / 4 * q ≤ Λ / 4 * 1 := mul_le_mul_of_nonneg_left hq1 (by positivity)
      _ = Λ / 4 := mul_one _
  obtain ⟨hlo, hhi⟩ := abs_le.mp hu
  -- Step 3: the key estimate `|e^u - 1| ≤ e^b b`.
  have hkey : |Real.exp u - 1| ≤ Real.exp b * b := by
    rcases le_total 0 u with h | h
    · -- `u ≥ 0`: multiplying `e^{-u} ≥ 1 - u` by `e^u` gives `e^u - 1 ≤ u e^u ≤ b e^b`.
      have h1 : 0 ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
      rw [abs_of_nonneg h1]
      have h2 : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
      have h3 : Real.exp u * Real.exp (-u) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h4 : Real.exp u - 1 ≤ u * Real.exp u := by
        have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos u).le
        nlinarith
      calc Real.exp u - 1 ≤ u * Real.exp u := h4
        _ ≤ b * Real.exp b := mul_le_mul hhi (Real.exp_le_exp.mpr hhi) (Real.exp_pos u).le hb0
        _ = Real.exp b * b := mul_comm _ _
    · -- `u ≤ 0`: `1 - e^u ≤ -u ≤ b ≤ e^b b`, by `e^u ≥ 1 + u` and `e^b ≥ 1`.
      have h1 : Real.exp u - 1 ≤ 0 := by
        have := Real.exp_le_one_iff.mpr h
        linarith
      rw [abs_of_nonpos h1]
      have h2 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
      have h3 : 1 ≤ Real.exp b := Real.one_le_exp hb0
      nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Step 2: `-Λ ≤ -b ≤ u ≤ b ≤ Λ/4 ≤ Λ`, and `exp` is monotone.
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.exp_le_exp.mpr (by linarith)
  -- Step 4: `e^b b ≤ e^{Λ/4} b = (e^{Λ/4}/4) Λ q ≤ (e^{Λ/2}/2) Λ q`.
  · have h1 : Real.exp (Λ / 4) ≤ Real.exp (Λ / 2) := Real.exp_le_exp.mpr (by linarith)
    have hΛq : 0 ≤ Λ * q := by positivity
    calc |Real.exp u - 1| ≤ Real.exp b * b := hkey
      _ ≤ Real.exp (Λ / 4) * b := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbΛ) hb0
      _ = Real.exp (Λ / 4) / 4 * (Λ * q) := by rw [hb]; ring
      _ ≤ Real.exp (Λ / 2) / 2 * (Λ * q) := by
          apply mul_le_mul_of_nonneg_right _ hΛq
          have := Real.exp_pos (Λ / 4)
          linarith
      _ = Real.exp (Λ / 2) / 2 * Λ * q := by ring
  -- Step 5: if `Λ ≤ 1`, then `|e^{Λ/4} - 1| ≤ 2 (Λ/4) ≤ 1/2`, so `e^{Λ/4} ≤ 4` and
  -- `|e^u - 1| ≤ 4 b = Λ q`.
  · intro hΛ1
    have h4 : Real.exp (Λ / 4) ≤ 4 := by
      have hΛ4 : (0 : ℝ) < Λ / 4 := by positivity
      have hx : |Λ / 4| ≤ 1 := by
        rw [abs_of_pos hΛ4]
        linarith
      have h := Real.abs_exp_sub_one_le hx
      rw [abs_of_pos hΛ4] at h
      have h2 := (abs_le.mp h).2
      linarith
    calc |Real.exp u - 1| ≤ Real.exp b * b := hkey
      _ ≤ Real.exp (Λ / 4) * b := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbΛ) hb0
      _ ≤ 4 * b := mul_le_mul_of_nonneg_right h4 hb0
      _ = Λ * q := by rw [hb]; ring
/-- **Simon Ch. 4, 4.3–4.8** (the integrating factor `F` and the limit `ε ↓ 0`, for abstract
sequences).  Let `R > 0`, `β < 1`, `Λ > 0` and `K R^{1−β}/(1 − β) ≤ Λ/4`.  Let `a_k, Q_k : ℝ → ℝ`
(`k ∈ ℕ`) and `a₀, Q₀ : ℝ → ℝ` satisfy, for `t ∈ (0, R]`: each `a_k` is a.e. strongly measurable on
`(0, R]`, `|a_k(t)| ≤ M t^{−β}`, `a_k(t) → a₀(t)`, `|a₀(t)| ≤ K t^{−β}` and `Q_k(t) → Q₀(t)`; and
let `e^{−∫₀ˢ a_k} Q_k(s) ≤ e^{−∫₀ʳ a_k} Q_k(r)` for `0 < s ≤ r ≤ R`.  Then `F(r) = e^{−∫₀ʳ a₀}`
satisfies `e^{−Λ} ≤ F(r) ≤ e^Λ`, `|F(r) − 1| ≤ ½ e^{Λ/2} Λ (r/R)^{1−β}` and, if `Λ ≤ 1`,
`|F(r) − 1| ≤ Λ (r/R)^{1−β}` for `0 < r ≤ R` (4.5–4.6), and `F(s) Q₀(s) ≤ F(r) Q₀(r)` for
`0 < s ≤ r ≤ R` (4.8).
Proof: `t ↦ C t^{−β}` is integrable on `[0, ρ]` because `−β > −1`.  For `0 < ρ ≤ R`, dominated
convergence with the majorant `M t^{−β}` gives `∫₀^ρ a_k → ∫₀^ρ a₀`, and
`|∫₀^ρ a₀| ≤ ∫₀^ρ K t^{−β} dt = K ρ^{1−β}/(1 − β) ≤ (Λ/4)(ρ/R)^{1−β}`.  The bounds on `F(r) = e^u`,
`u = −∫₀ʳ a₀`, are `ted_lpm_am_exp_perturbation_bounds` with `q = (r/R)^{1−β}`.  The monotonicity
of `F Q₀` follows by letting `k → ∞` in the monotonicity for each `k`. -/
theorem ted_lpm_am_integrating_factor_limit : ∀ (R β M K Λ : ℝ) (a : ℕ → ℝ → ℝ) (a₀ : ℝ → ℝ) (Q : ℕ → ℝ → ℝ) (Q₀ : ℝ → ℝ), 0 < R → β < 1 → 0 < Λ → K * R ^ (1 - β) / (1 - β) ≤ Λ / 4 → (∀ k, AEStronglyMeasurable (a k) (volume.restrict (Ioc 0 R))) → (∀ k t, 0 < t → t ≤ R → |a k t| ≤ M * t ^ (-β)) → (∀ t, 0 < t → t ≤ R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t))) → (∀ t, 0 < t → t ≤ R → |a₀ t| ≤ K * t ^ (-β)) → (∀ t, 0 < t → t ≤ R → Tendsto (fun k => Q k t) atTop (𝓝 (Q₀ t))) → (∀ k s r, 0 < s → s ≤ r → r ≤ R → Real.exp (-∫ t in (0)..s, a k t) * Q k s ≤ Real.exp (-∫ t in (0)..r, a k t) * Q k r) → (∀ r, 0 < r → r ≤ R → Real.exp (-Λ) ≤ Real.exp (-∫ t in (0)..r, a₀ t) ∧ Real.exp (-∫ t in (0)..r, a₀ t) ≤ Real.exp Λ ∧ |Real.exp (-∫ t in (0)..r, a₀ t) - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (r / R) ^ (1 - β) ∧ (Λ ≤ 1 → |Real.exp (-∫ t in (0)..r, a₀ t) - 1| ≤ Λ * (r / R) ^ (1 - β))) ∧ (∀ s r, 0 < s → s ≤ r → r ≤ R → Real.exp (-∫ t in (0)..s, a₀ t) * Q₀ s ≤ Real.exp (-∫ t in (0)..r, a₀ t) * Q₀ r) := by
  intro R β M K Λ a a₀ Q Q₀ hR hβ hΛ hK ha_meas ha_bd ha_lim ha₀_bd hQ_lim hmono
  have hβ' : 0 < 1 - β := sub_pos.mpr hβ
  -- Step 1: `t ↦ C t^{−β}` is interval integrable on `[0, ρ]`, since `−β > −1`.
  have hmaj : ∀ C ρ : ℝ, IntervalIntegrable (fun t => C * t ^ (-β)) volume 0 ρ := fun C ρ =>
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C
  -- Step 2: for `0 < ρ ≤ R`, dominated convergence on `(0, ρ] ⊆ (0, R]` with the majorant
  -- `M t^{−β}` gives `∫₀^ρ a_k → ∫₀^ρ a₀`.
  have hlim : ∀ ρ, 0 < ρ → ρ ≤ R →
      Tendsto (fun k => ∫ t in (0)..ρ, a k t) atTop (𝓝 (∫ t in (0)..ρ, a₀ t)) := by
    intro ρ hρ hρR
    have hsub : uIoc 0 ρ ⊆ Ioc 0 R := by
      rw [uIoc_of_le hρ.le]
      exact Ioc_subset_Ioc_right hρR
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t => M * t ^ (-β)) (Eventually.of_forall fun k => ?_)
      (Eventually.of_forall fun k => ae_of_all _ fun t ht => ?_) (hmaj M ρ)
      (ae_of_all _ fun t ht => ha_lim t (hsub ht).1 (hsub ht).2)
    · exact (ha_meas k).mono_measure (Measure.restrict_mono hsub le_rfl)
    · rw [Real.norm_eq_abs]
      exact ha_bd k t (hsub ht).1 (hsub ht).2
  -- Step 3: for `0 < ρ ≤ R`, `|∫₀^ρ a₀| ≤ K ρ^{1−β}/(1 − β) ≤ (Λ/4)(ρ/R)^{1−β}`.
  have hbound : ∀ ρ, 0 < ρ → ρ ≤ R → |∫ t in (0)..ρ, a₀ t| ≤ Λ / 4 * (ρ / R) ^ (1 - β) := by
    intro ρ hρ hρR
    have h1 : ‖∫ t in (0)..ρ, a₀ t‖ ≤ ∫ t in (0)..ρ, K * t ^ (-β) :=
      intervalIntegral.norm_integral_le_of_norm_le hρ.le
        (ae_of_all _ fun t ht => by
          rw [Real.norm_eq_abs]
          exact ha₀_bd t ht.1 (ht.2.trans hρR))
        (hmaj K ρ)
    have h2 : ∫ t in (0)..ρ, K * t ^ (-β) = K * ρ ^ (1 - β) / (1 - β) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
        show -β + 1 = 1 - β by ring, Real.zero_rpow hβ'.ne', sub_zero, mul_div_assoc]
    have h3 : K * ρ ^ (1 - β) / (1 - β) = K * R ^ (1 - β) / (1 - β) * (ρ / R) ^ (1 - β) := by
      have hRβ : 0 < R ^ (1 - β) := Real.rpow_pos_of_pos hR _
      rw [Real.div_rpow hρ.le hR.le]
      field_simp
    rw [← Real.norm_eq_abs]
    calc ‖∫ t in (0)..ρ, a₀ t‖ ≤ K * ρ ^ (1 - β) / (1 - β) := h1.trans_eq h2
      _ = K * R ^ (1 - β) / (1 - β) * (ρ / R) ^ (1 - β) := h3
      _ ≤ Λ / 4 * (ρ / R) ^ (1 - β) :=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (div_nonneg hρ.le hR.le) _)
  refine ⟨fun r hr hrR => ?_, fun s r hs hsr hrR => ?_⟩
  -- Step 4: (i) is `ted_lpm_am_exp_perturbation_bounds` with `q = (r/R)^{1−β} ∈ [0, 1]` and
  -- `u = −∫₀ʳ a₀`, for which `|u| ≤ (Λ/4) q` by Step 3.
  · have hq0 : 0 ≤ (r / R) ^ (1 - β) := Real.rpow_nonneg (div_nonneg hr.le hR.le) _
    have hq1 : (r / R) ^ (1 - β) ≤ 1 :=
      Real.rpow_le_one (div_nonneg hr.le hR.le) ((div_le_one hR).mpr hrR) hβ'.le
    have hu : |-∫ t in (0)..r, a₀ t| ≤ Λ / 4 * (r / R) ^ (1 - β) := by
      rw [abs_neg]
      exact hbound r hr hrR
    exact Submission.ted_lpm_am_exp_perturbation_bounds Λ _ _ hΛ hq0 hq1 hu
  -- Step 5: (ii).  By Step 2, continuity of `exp` and the convergence of `Q_k`,
  -- `e^{−∫₀^ρ a_k} Q_k(ρ) → F(ρ) Q₀(ρ)` for `ρ ∈ {s, r}`; the inequality for each `k` passes
  -- to the limit.
  · have hΨ : ∀ ρ, 0 < ρ → ρ ≤ R →
        Tendsto (fun k => Real.exp (-∫ t in (0)..ρ, a k t) * Q k ρ) atTop
          (𝓝 (Real.exp (-∫ t in (0)..ρ, a₀ t) * Q₀ ρ)) := fun ρ hρ hρR =>
      ((Real.continuous_exp.tendsto _).comp (hlim ρ hρ hρR).neg).mul (hQ_lim ρ hρ hρR)
    exact le_of_tendsto_of_tendsto' (hΨ s hs (hsr.trans hrR)) (hΨ r (hs.trans_le hsr) hrR)
      fun k => hmono k s r hs hsr hrR
/-- **Simon Ch. 4, 4.2–4.3** (the Hölder step for the mean-curvature term).  Let `p > 1`, let `μ`
be a measure on `ℝ^{n+ℓ}` with `μ(B_t(y)) < ∞`, let `H` be `μ`-integrable on `B_t(y)` with
`J = ∫_{B_t(y)} |H|ᵖ dμ < ∞`, and let `ψ` be a.e. strongly measurable with `0 ≤ ψ ≤ 1` and `ψ = 0`
off `B_t(y)`.  Then `|∫ ψ(x) (x − y) · H(x) dμ| ≤ t J^{1/p} (∫ ψ dμ)^{1 − 1/p}`.
Proof: on `B_t(y)`, `|ψ(x) (x − y) · H(x)| ≤ t |H(x)| ψ(x)` by Cauchy–Schwarz, and the pairing
vanishes off `B_t(y)`.  Hölder on `B_t(y)` with `q = p/(p − 1)`, together with `ψ^q ≤ ψ`, bounds
`∫_{B_t(y)} |H| ψ dμ` by `J^{1/p} (∫ ψ dμ)^{1/q}`.  The estimate is proved in `[0, ∞]`, where the
bound is finite, and then converted to real numbers. -/
theorem ted_lpm_curvature_holder : ∀ (n ℓ : ℕ) (p : ℝ), 1 < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (ψ : Amb n ℓ → ℝ) (y : Amb n ℓ) (t : ℝ), 0 ≤ t → μ (closedBall y t) < ⊤ → IntegrableOn H (closedBall y t) μ → ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ < ⊤ → AEStronglyMeasurable ψ μ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → (∀ x, t < ‖x - y‖ → ψ x = 0) → |∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ| ≤ t * (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
  intro n ℓ p hp μ H ψ y t ht hμB hHint hHp hψm hψ01 hψt
  -- Notation: `B = B_t(y)`, a closed (hence measurable) ball.
  set B : Set (Amb n ℓ) := closedBall y t
  have hBm : MeasurableSet B := measurableSet_closedBall
  -- Step 1: the conjugate exponent `q = p/(p - 1)`, so `q > 1` and `1/q = 1 - 1/p`.
  obtain ⟨q, hpq⟩ : ∃ q : ℝ, p.HolderConjugate q :=
    ⟨p / (p - 1), Real.HolderConjugate.conjExponent hp⟩
  have hq1 : 1 - 1 / p = 1 / q := by rw [one_div, one_div, hpq.one_sub_inv]
  -- Step 2: `ψ` vanishes off `B`.
  have hψB : ∀ x, x ∉ B → ψ x = 0 := fun x hx =>
    hψt x (by simpa [B, mem_closedBall, dist_eq_norm] using hx)
  -- Step 3: `ψ` is bounded by `1` on `B` and `μ(B) < ∞`, so `ψ` is integrable on `B`; it vanishes
  -- off `B`, so it is `μ`-integrable.  Its integral is nonnegative and equals `∫⁻ ‖ψ‖ₑ dμ`.
  have hψe : ∀ x, ‖ψ x‖ₑ = ENNReal.ofReal (ψ x) := fun x => Real.enorm_of_nonneg (hψ01 x).1
  have hψle : ∀ x, ‖ψ x‖ₑ ≤ 1 := fun x => (hψe x).trans_le (ENNReal.ofReal_le_one.2 (hψ01 x).2)
  have hψint : Integrable ψ μ :=
    (IntegrableOn.of_bound hμB hψm.restrict 1 (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (hψ01 x).1]
      exact (hψ01 x).2)).integrable_of_forall_notMem_eq_zero hψB
  have hψnn : 0 ≤ ∫ x, ψ x ∂μ := integral_nonneg fun x => (hψ01 x).1
  have hψI : ∫⁻ x, ‖ψ x‖ₑ ∂μ = ENNReal.ofReal (∫ x, ψ x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hψint (ae_of_all _ fun x => (hψ01 x).1)]
    exact lintegral_congr hψe
  -- Step 4: on `B`, `|ψ(x)(x - y)·H(x)| ≤ t |H(x)| ψ(x)` by Cauchy–Schwarz and `|x - y| ≤ t`;
  -- off `B` the pairing vanishes.
  have hpt : ∀ x, ‖ψ x * inner ℝ (x - y) (H x)‖ₑ ≤
      B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      have hxy : ‖x - y‖ ≤ t := by simpa [B, mem_closedBall, dist_eq_norm] using hx
      have hreal : ‖ψ x * inner ℝ (x - y) (H x)‖ ≤ t * (‖H x‖ * ψ x) := by
        rw [norm_mul, Real.norm_of_nonneg (hψ01 x).1]
        calc ψ x * ‖inner ℝ (x - y) (H x)‖ ≤ ψ x * (‖x - y‖ * ‖H x‖) :=
              mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (hψ01 x).1
          _ ≤ ψ x * (t * ‖H x‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxy (norm_nonneg _))
                (hψ01 x).1
          _ = t * (‖H x‖ * ψ x) := by ring
      calc ‖ψ x * inner ℝ (x - y) (H x)‖ₑ = ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ :=
            (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (t * (‖H x‖ * ψ x)) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ) := by
          rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, hψe]
    · rw [indicator_of_notMem hx, hψB x hx, zero_mul, enorm_zero]
  -- Step 6: Hölder's inequality on `(B, μ⌞B)` with exponents `p` and `q`.
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict B) hpq
    hHint.aestronglyMeasurable.enorm hψm.restrict.enorm
  simp only [Pi.mul_apply] at hHolder
  -- Step 7: `ψ^q ≤ ψ` since `0 ≤ ψ ≤ 1` and `q ≥ 1`, so `∫_B ψ^q ≤ ∫_B ψ ≤ ∫ ψ`.
  have hψq : ∫⁻ x in B, ‖ψ x‖ₑ ^ q ∂μ ≤ ENNReal.ofReal (∫ x, ψ x ∂μ) :=
    calc ∫⁻ x in B, ‖ψ x‖ₑ ^ q ∂μ ≤ ∫⁻ x in B, ‖ψ x‖ₑ ∂μ :=
          lintegral_mono fun x => ENNReal.rpow_le_self_of_le_one (hψle x) hpq.symm.lt.le
      _ ≤ ∫⁻ x, ‖ψ x‖ₑ ∂μ := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ x, ψ x ∂μ) := hψI
  -- Steps 5 and 8: integrate the pointwise bound, then apply Steps 6 and 7, all in `[0, ∞]`.
  have key : ‖∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ‖ₑ ≤ ENNReal.ofReal t *
      ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) :=
    calc ‖∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ‖ₑ
        ≤ ∫⁻ x, ‖ψ x * inner ℝ (x - y) (H x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ)) x ∂μ :=
          lintegral_mono hpt
      _ = ∫⁻ x in B, ENNReal.ofReal t * (‖H x‖ₑ * ‖ψ x‖ₑ) ∂μ := lintegral_indicator hBm _
      _ = ENNReal.ofReal t * ∫⁻ x in B, ‖H x‖ₑ * ‖ψ x‖ₑ ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal t *
          ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * (∫⁻ x in B, ‖ψ x‖ₑ ^ q ∂μ) ^ (1 / q)) := by
          gcongr ENNReal.ofReal t * ?_
      _ ≤ ENNReal.ofReal t *
          ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) := by
          gcongr ENNReal.ofReal t * (_ * ?_)
          exact ENNReal.rpow_le_rpow hψq hpq.symm.one_div_nonneg
  -- Step 9: the bound is finite (`J < ∞`), so `toReal` is monotone on it; `toReal` is
  -- multiplicative and commutes with real powers, and `1/q = 1 - 1/p` by Step 1.
  have hfin : ENNReal.ofReal t *
      ((∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpq.one_div_nonneg hHp.ne)
        (ENNReal.rpow_ne_top_of_nonneg hpq.symm.one_div_nonneg ENNReal.ofReal_ne_top))
  have h := ENNReal.toReal_mono hfin key
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal ht, ENNReal.toReal_ofReal hψnn,
    Real.norm_eq_abs] at h
  rw [hq1, mul_assoc]
  exact h
/-- Simon Ch. 4, (4.3)–(4.4), in abstract form (`P = I'`, and `Q` plays the role of `J'`): if on
`(0, R)` we have `I' = P`, `L` continuous, `I ≥ 0`, `nI − tP + tQ = −L`,
`a = (L/t^{n+1})/(1 + I/tⁿ)` and `|a| ≤ M t^{−β}` with `β < 1`, then
`Ψ(s) = exp(−∫₀ˢ a)(1 + I(s)/sⁿ)` satisfies `Ψ'(t) = exp(−∫₀ᵗ a) Q(t)/tⁿ`, and
`exp(−∫₀^ρ |a|) ≤ exp(−∫₀ᵗ a) ≤ exp(∫₀^ρ |a|)` for `0 < t ≤ ρ < R`. -/
theorem aal_cfs_integrating_factor_deriv : ∀ (n : ℕ) (I L a P Q : ℝ → ℝ) (R M β : ℝ), β < 1 → (∀ t : ℝ, 0 < t → t < R → HasDerivAt I (P t) t) → (∀ t : ℝ, 0 < t → t < R → ContinuousAt L t) → (∀ t : ℝ, 0 < t → t < R → 0 ≤ I t) → (∀ t : ℝ, 0 < t → t < R → (n : ℝ) * I t - t * P t + t * Q t = -L t) → (∀ t : ℝ, 0 < t → t < R → a t = L t / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → t < R → |a t| ≤ M * t ^ (-β)) → (∀ t : ℝ, 0 < t → t < R → HasDerivAt (fun s => Real.exp (-∫ u in (0)..s, a u) * (1 + I s / s ^ n)) (Real.exp (-∫ u in (0)..t, a u) * (Q t / t ^ n)) t) ∧ (∀ t ρ : ℝ, 0 < t → t ≤ ρ → ρ < R → Real.exp (-∫ u in (0)..ρ, |a u|) ≤ Real.exp (-∫ u in (0)..t, a u) ∧ Real.exp (-∫ u in (0)..t, a u) ≤ Real.exp (∫ u in (0)..ρ, |a u|)) := by
  intro n I L a P Q R M β hβ hIder hLc hInn hid ha hab
  have hden : ∀ t, 0 < t → t < R → 1 ≤ 1 + I t / t ^ n := fun t ht htR => by
    have := div_nonneg (hInn t ht htR) (pow_pos ht n).le
    linarith
  -- `a` is continuous on `(0, R)`
  have hacontAt : ∀ t, 0 < t → t < R → ContinuousAt a t := by
    intro t ht htR
    have hev : (fun s => L s / s ^ (n + 1) / (1 + I s / s ^ n)) =ᶠ[𝓝 t] a := by
      filter_upwards [Ioo_mem_nhds ht htR] with s hs
      exact (ha s hs.1 hs.2).symm
    refine ContinuousAt.congr ?_ hev
    exact ((hLc t ht htR).div ((continuous_pow (n + 1)).continuousAt)
      (pow_ne_zero _ ht.ne')).div
      (continuousAt_const.add ((hIder t ht htR).continuousAt.div
        ((continuous_pow n).continuousAt) (pow_ne_zero _ ht.ne')))
      (by linarith [hden t ht htR])
  have hacont : ContinuousOn a (Ioo 0 R) := fun t ht =>
    (hacontAt t ht.1 ht.2).continuousWithinAt
  -- `a` is integrable on `[0, t]`, by the bound `|a s| ≤ M s^(-β)` with `β < 1`
  have haint : ∀ t, 0 < t → t < R → IntervalIntegrable a volume 0 t := by
    intro t ht htR
    refine IntervalIntegrable.mono_fun' (g := fun s => M * s ^ (-β)) ?_ ?_ ?_
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul M
    · rw [uIoc_of_le ht.le]
      exact (hacont.mono (Ioc_subset_Ioo_right htR)).aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le ht.le]
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
      show ‖a s‖ ≤ M * s ^ (-β)
      rw [Real.norm_eq_abs]
      exact hab s hs.1 (lt_of_le_of_lt hs.2 htR)
  -- the fundamental theorem of calculus for `∫₀ᵗ a`
  have hGderiv : ∀ t, 0 < t → t < R → HasDerivAt (fun u => ∫ s in (0)..u, a s) (a t) t := by
    intro t ht htR
    exact intervalIntegral.integral_hasDerivAt_right (haint t ht htR)
      (hacont.stronglyMeasurableAtFilter isOpen_Ioo t ⟨ht, htR⟩) (hacontAt t ht htR)
  refine ⟨fun t ht htR => ?_, fun t ρ ht htρ hρR => ?_⟩
  · have hd := ((hGderiv t ht htR).neg.exp).mul ((hasDerivAt_const t (1 : ℝ)).add
      ((hIder t ht htR).div (hasDerivAt_pow n t) (pow_ne_zero n ht.ne')))
    have hd' : HasDerivAt (fun s => Real.exp (-∫ u in (0)..s, a u) * (1 + I s / s ^ n))
        (Real.exp (-∫ u in (0)..t, a u) * -a t * (1 + I t / t ^ n) +
          Real.exp (-∫ u in (0)..t, a u) *
            (0 + (P t * t ^ n - I t * ((n : ℝ) * t ^ (n - 1))) / (t ^ n) ^ 2)) t := hd
    convert hd' using 1
    set E := Real.exp (-∫ u in (0)..t, a u) with hEdef
    have hP : 0 < t ^ n := pow_pos ht n
    have hden' : 1 + I t / t ^ n ≠ 0 := by linarith [hden t ht htR]
    have haL : a t * (1 + I t / t ^ n) = L t / (t ^ n * t) := by
      rw [ha t ht htR, div_mul_cancel₀ _ hden', pow_succ]
    have hnpow : (n : ℝ) * t ^ (n - 1) = n * t ^ n / t := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · rw [eq_div_iff ht.ne', mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
    have hq : (P t * t ^ n - I t * ((n : ℝ) * t ^ (n - 1))) / (t ^ n) ^ 2 =
        (t * P t - n * I t) / (t ^ n * t) := by
      rw [hnpow]
      field_simp
    have hidt : t * P t - n * I t = t * Q t + L t := by linarith [hid t ht htR]
    have hQ : (t * Q t + L t) / (t ^ n * t) = Q t / t ^ n + L t / (t ^ n * t) := by
      field_simp
    rw [hq, hidt, hQ]
    linear_combination E * haL
  · have hiρ := haint ρ (ht.trans_le htρ) hρR
    have h1 : |∫ u in (0)..t, a u| ≤ ∫ u in (0)..t, |a u| :=
      intervalIntegral.abs_integral_le_integral_abs ht.le
    have h2 : ∫ u in (0)..t, |a u| ≤ ∫ u in (0)..ρ, |a u| :=
      intervalIntegral.integral_mono_interval le_rfl ht.le htρ
        (Eventually.of_forall fun u => abs_nonneg _) hiρ.abs
    have h3 := abs_le.mp (h1.trans h2)
    exact ⟨Real.exp_le_exp.mpr (by linarith [h3.2]), Real.exp_le_exp.mpr (by linarith [h3.1])⟩
/-- Differentiation in the scale of a radial cutoff integral (step 2(c) of the annular
monotonicity proof, part (c) of `allard52_am_cutoff_integral_calculus`): if `f` is
`μ`-integrable on `B_S(y)`, `φ` is `C¹` with `φ = 0` on `[T, ∞)`, `T > 0`, `t > 0` and `T t < S`,
then `s ↦ ∫ φ(‖x − y‖/s) f(x) dμ` has derivative `-(∫ (‖x − y‖/t) φ'(‖x − y‖/t) f(x) dμ)/t` at `t`.
For `0 < s < S/T` the integrands vanish off `B_S(y)`; on `(t/2, S/T)` the `s`-derivatives are
bounded by `(2 C₁/t) |f|` with `C₁ = max_{[0,T]} |u φ'(u)|`, and one differentiates under the
integral sign against `μ ⌞ B_S(y)`. -/
theorem allard52_am_cc_cutoff_integral_hasDerivAt : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (f : Amb n ℓ → ℝ) (φ : ℝ → ℝ) (S T t : ℝ), IntegrableOn f (closedBall y S) μ → ContDiff ℝ 1 φ → 0 < T → (∀ u : ℝ, T ≤ u → φ u = 0) → 0 < t → T * t < S → HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) * f x ∂μ) (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ) / t) t := by
  intro n ℓ μ y f φ S T t hf hφ hT hφ0 ht htS
  set K : Set (Amb n ℓ) := closedBall y S with hK
  set ν : Measure (Amb n ℓ) := μ.restrict K with hν
  have hfν : Integrable f ν := hf
  have hφc : Continuous φ := hφ.continuous
  have hdφc : Continuous (deriv φ) := hφ.continuous_deriv_one
  -- Step 2: `φ' = 0` on `(T, ∞)`.
  have hdzero : ∀ u, T < u → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [lt_mem_nhds hu] with v hv
      exact hφ0 v hv.le
    exact h.deriv_eq.trans (deriv_const u 0)
  -- Step 3: `|φ u| ≤ C₀` and `|u φ'(u)| ≤ C₁` for `u ≥ 0`.
  obtain ⟨C₀, hC₀⟩ : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |φ u| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      hφc.continuousOn
    refine ⟨max C 0, fun u hu => ?_⟩
    rcases le_or_gt u T with h | h
    · have h' := hC u ⟨hu, h⟩
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    · rw [hφ0 u h.le, abs_zero]
      exact le_max_right _ _
  obtain ⟨C₁, hC₁0, hC₁⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → |u * deriv φ u| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      (continuous_id.mul hdφc).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun u hu => ?_⟩
    rcases le_or_gt u T with h | h
    · have h' := hC u ⟨hu, h⟩
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    · rw [hdzero u h, mul_zero, abs_zero]
      exact le_max_right _ _
  -- Step 5: `d/ds φ(r/s) = -(r/s) φ'(r/s) / s` for `s ≠ 0`.
  have hderiv : ∀ (r s : ℝ), s ≠ 0 →
      HasDerivAt (fun u => φ (r / u)) (-(r / s * deriv φ (r / s)) / s) s := by
    intro r s hs
    have h1 : HasDerivAt (fun u : ℝ => r / u) (r * -(s ^ 2)⁻¹) s := by
      have := (hasDerivAt_inv hs).const_mul r
      convert this using 1
      funext u
      exact div_eq_mul_inv r u
    have h2 := ((hφ.differentiable (by simp) (r / s)).hasDerivAt).comp s h1
    have heq : -(r / s * deriv φ (r / s)) / s = deriv φ (r / s) * (r * -(s ^ 2)⁻¹) := by
      rw [sq, mul_inv]
      ring
    rw [heq]
    exact h2
  -- Step 1: `t < R := S / T`; we work on the neighbourhood `(t/2, R)` of `t`.
  set R : ℝ := S / T with hR
  have hRiff : ∀ s : ℝ, s < R ↔ T * s < S := fun s => by
    rw [hR, lt_div_iff₀ hT, mul_comm]
  have htR : t < R := (hRiff t).2 htS
  -- Step 2: for `0 < s < R` the integrands vanish off `K = B_S(y)`.
  have hout : ∀ s, 0 < s → s < R → ∀ x, x ∉ K → T < ‖x - y‖ / s := by
    intro s hs hsR x hx
    have hxS : S < ‖x - y‖ := by
      simpa [hK, mem_closedBall, dist_eq_norm, not_le] using hx
    rw [lt_div_iff₀ hs]
    linarith [(hRiff s).1 hsR]
  have hconv : ∀ s, 0 < s → s < R →
      ∫ x, φ (‖x - y‖ / s) * f x ∂μ = ∫ x, φ (‖x - y‖ / s) * f x ∂ν := by
    intro s hs hsR
    rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [hφ0 _ (hout s hs hsR x hx).le, zero_mul]
  have hconv' : ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ =
      ∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂ν := by
    rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [hdzero _ (hout t ht htR x hx), mul_zero, zero_mul]
  -- Step 4: measurability, and integrability of the integrand at `t`, for `ν`.
  have hmeas : ∀ s, AEStronglyMeasurable (fun x => φ (‖x - y‖ / s) * f x) ν := fun s =>
    (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / s)).aestronglyMeasurable.mul
      hfν.aestronglyMeasurable
  have hint : Integrable (fun x => φ (‖x - y‖ / t) * f x) ν := by
    refine Integrable.mono' (hfν.norm.const_mul C₀) (hmeas t) ?_
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC₀ _ (div_nonneg (norm_nonneg _) ht.le)) (norm_nonneg _)
  -- Step 6: differentiation under the integral sign for `ν` on `(t/2, R)`, bound `(2C₁/t)‖f‖`.
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun s x => φ (‖x - y‖ / s) * f x)
    (F' := fun s x => -(‖x - y‖ / s * deriv φ (‖x - y‖ / s)) / s * f x)
    (x₀ := t) (bound := fun x => 2 * C₁ / t * ‖f x‖) (s := Ioo (t / 2) R)
    (Ioo_mem_nhds (half_lt_self ht) htR) (Eventually.of_forall hmeas) hint ?_ ?_
    (hfν.norm.const_mul _) ?_
  -- Step 7: evaluate the derivative and transfer from `ν` back to `μ` near `t`.
  · have hderivν := key.2
    have heq : (∫ x, -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t * f x ∂ν) =
        -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) * f x ∂μ) / t := by
      rw [hconv', ← integral_neg, ← integral_div]
      congr 1
      funext x
      ring
    rw [heq] at hderivν
    refine hderivν.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht htR] with s hs
    exact hconv s hs.1 hs.2
  · exact (by fun_prop : Continuous fun x : Amb n ℓ =>
      -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t).aestronglyMeasurable.mul hfν.aestronglyMeasurable
  · refine Eventually.of_forall fun x s hs => ?_
    have hs0 : 0 < s := lt_trans (half_pos ht) hs.1
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hs0]
    have h1 : |‖x - y‖ / s * deriv φ (‖x - y‖ / s)| / s ≤ 2 * C₁ / t := by
      rw [div_le_div_iff₀ hs0 ht]
      have := hC₁ _ (div_nonneg (norm_nonneg (x - y)) hs0.le)
      nlinarith [hs.1]
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  · refine Eventually.of_forall fun x s hs => ?_
    have hs0 : 0 < s := lt_trans (half_pos ht) hs.1
    exact (hderiv ‖x - y‖ s hs0.ne').mul_const (f x)

end Submission

namespace Submission

/-- Integrability of a continuous radial profile vanishing beyond `T` (the integrability parts (a)
and (b) of `ted_lpm_fcm_cutoff_mass_hasDerivAt`): if `μ(B_S(y)) < ∞`, `g` is continuous with
`g = 0` on `(T, ∞)`, `t > 0` and `T t < S`, then `x ↦ g(‖x − y‖/t)` is `μ`-integrable.
It is bounded by `K = max(max_{[0,T]} |g|, 0)`, hence integrable on `B_S(y)`, and it vanishes off
`B_S(y)`, where `‖x − y‖/t > S/t > T`. -/
theorem ted_lpm_fcm_cmd_radial_integrable : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (g : ℝ → ℝ) (S T t : ℝ), μ (closedBall y S) < ⊤ → Continuous g → (∀ u : ℝ, T < u → g u = 0) → 0 < t → T * t < S → Integrable (fun x => g (‖x - y‖ / t)) μ := by
  intro n ℓ μ y g S T t hμ hg hg0 ht htS
  -- Step 1: `|g u| ≤ K` for `u ≥ 0`.
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ K := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
      hg.continuousOn
    refine ⟨max C 0, fun u hu => ?_⟩
    rcases le_or_gt u T with h | h
    · have h' := hC u ⟨hu, h⟩
      rw [Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    · rw [hg0 u h, abs_zero]
      exact le_max_right _ _
  -- Step 2: `x ↦ g(‖x − y‖/t)` is continuous, hence a.e.-strongly measurable.
  have hmeas : AEStronglyMeasurable (fun x => g (‖x - y‖ / t)) (μ.restrict (closedBall y S)) :=
    (hg.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
  -- Steps 3–4: it is bounded by `K`, hence integrable on `B_S(y)`, which has finite measure.
  have hon : IntegrableOn (fun x => g (‖x - y‖ / t)) (closedBall y S) μ := by
    refine IntegrableOn.of_bound hμ hmeas K (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hK _ (div_nonneg (norm_nonneg _) ht.le)
  -- Steps 5–6: off `B_S(y)` we have `‖x − y‖/t > T`, so the integrand vanishes there.
  refine hon.integrable_of_forall_notMem_eq_zero fun x hx => hg0 _ ?_
  have hxS : S < ‖x - y‖ := by
    simpa [mem_closedBall, dist_eq_norm, not_le] using hx
  rw [lt_div_iff₀ ht]
  linarith

end Submission

namespace Submission

/-- Derivative of the radial cutoff mass `I(s) = ∫ φ(‖x − y‖/s) dμ` (Simon Ch. 4, 4.3), together
with the integrability of its two radial profiles: if `μ(B_S(y)) < ∞`, `φ` is `C¹` with `φ = 0` on
`[T, ∞)`, `T > 0`, `t > 0` and `T t < S`, then `φ(‖x − y‖/t)` and `(‖x − y‖/t) φ'(‖x − y‖/t)` are
`μ`-integrable and `I'(t) = -(∫ (‖x − y‖/t) φ'(‖x − y‖/t) dμ)/t`.  The profiles `φ` and
`u ↦ u φ'(u)` are continuous and vanish on `(T, ∞)` (where `φ' = 0`), so
`ted_lpm_fcm_cmd_radial_integrable` gives both integrability statements; the derivative is the
weight-`1` case of `allard52_am_cc_cutoff_integral_hasDerivAt`, as `1` is integrable on the
finite-measure ball `B_S(y)`. -/
theorem ted_lpm_fcm_cutoff_mass_hasDerivAt : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (φ : ℝ → ℝ) (S T t : ℝ), 0 < T → μ (closedBall y S) < ⊤ → ContDiff ℝ 1 φ → (∀ u : ℝ, T ≤ u → φ u = 0) → 0 < t → T * t < S → Integrable (fun x => φ (‖x - y‖ / t)) μ ∧ Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) μ ∧ HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) ∂μ) (-(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ) / t) t := by
  intro n ℓ μ y φ S T t hT hμ hφ hφ0 ht htS
  -- `φ' = 0` on `(T, ∞)`: near each such point `φ` is the zero function.
  have hdzero : ∀ u, T < u → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [lt_mem_nhds hu] with v hv
      exact hφ0 v hv.le
    exact h.deriv_eq.trans (deriv_const u 0)
  refine ⟨?_, ?_, ?_⟩
  -- (a): the continuous profile `φ` vanishes on `(T, ∞)`.
  · exact ted_lpm_fcm_cmd_radial_integrable n ℓ μ y φ S T t hμ hφ.continuous
      (fun u hu => hφ0 u hu.le) ht htS
  -- (b): so does the continuous profile `u ↦ u φ'(u)`.
  · exact ted_lpm_fcm_cmd_radial_integrable n ℓ μ y (fun u => u * deriv φ u) S T t hμ
      (continuous_id.mul hφ.continuous_deriv_one) (fun u hu => by simp only [hdzero u hu, mul_zero])
      ht htS
  -- (c): the weighted cutoff derivative with weight `1`.
  · simpa only [mul_one] using allard52_am_cc_cutoff_integral_hasDerivAt n ℓ μ y
      (fun _ => 1) φ S T t (integrableOn_const hμ.ne) hφ hT hφ0 ht htS
/-- Simon Ch. 4, 4.3–4.4 (continuity in the scale of the cutoff pairing): let `φ` be continuous
with `φ = 0` on `[T, ∞)` for some `T > 0`, and let `H` be `μ`-integrable on `B_S(y)`.  Then
`L(s) = ∫ φ(‖x − y‖/s) (x − y)·H(x) dμ(x)` is continuous at every `t > 0` with `T t < S`.
`|φ| ≤ K` on `[0, ∞)` (a bound on the compact `[0, T]`); for `0 < s < S/T` the integrand vanishes
off `B_S(y)` and is bounded there by `K S ‖H‖`, so dominated convergence applies to `μ ⌞ B_S(y)`. -/
theorem ted_lpm_fcm_cutoff_pairing_continuousAt : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (φ : ℝ → ℝ) (S T t : ℝ), 0 < T → IntegrableOn H (closedBall y S) μ → Continuous φ → (∀ u : ℝ, T ≤ u → φ u = 0) → 0 < t → T * t < S → ContinuousAt (fun s => ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂μ) t := by
  intro n ℓ μ H y φ S T t hT hH hφc hzero ht htS
  have hHν : Integrable H (μ.restrict (closedBall y S)) := hH
  -- Step 1: `|φ| ≤ K` on `[0, ∞)`: `φ` is bounded on the compact `[0, T]` and vanishes beyond `T`.
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφc.continuousOn (s := Icc 0 T))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, hT.le⟩)
  have hφK : ∀ u, 0 ≤ u → ‖φ u‖ ≤ K := fun u hu => by
    rcases le_or_gt u T with h | h
    · exact hK u ⟨hu, h⟩
    · rw [hzero u h.le, norm_zero]
      exact hK0
  -- `t < S/T`.
  have htR : t < S / T := by
    rw [lt_div_iff₀ hT]
    linarith
  -- Step 2: for `s ∈ (0, S/T)` the integrand vanishes off `B_S(y)` (there `‖x − y‖/s ≥ T`),
  -- so `L(s)` is the integral against `μ ⌞ B_S(y)`.
  have hconv : ∀ s ∈ Ioo 0 (S / T),
      ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂(μ.restrict (closedBall y S)) =
        ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂μ := by
    rintro s ⟨hs, hsR⟩
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rw [lt_div_iff₀ hT] at hsR
    have h1 : T ≤ ‖x - y‖ / s := by
      rw [le_div_iff₀ hs]
      linarith
    rw [hzero _ h1, zero_mul]
  -- Step 3: dominated convergence for the `μ ⌞ B_S(y)`-integral at `t`, with bound `K S ‖H‖`.
  have hmain : ContinuousAt (fun s =>
      ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂(μ.restrict (closedBall y S))) t := by
    refine continuousAt_of_dominated (bound := fun x => K * S * ‖H x‖) ?_ ?_
      (hHν.norm.const_mul (K * S)) ?_
    · -- Measurability: `x ↦ φ(‖x − y‖/s)` is continuous and `x ↦ (x − y)·H(x)` is
      -- a.e. strongly measurable.
      refine Eventually.of_forall fun s => ?_
      have hcut : Continuous fun x : Amb n ℓ => φ (‖x - y‖ / s) := hφc.comp (by fun_prop)
      exact hcut.aestronglyMeasurable.mul
        (continuous_inner.comp_aestronglyMeasurable
          ((by fun_prop : Continuous fun x : Amb n ℓ => x - y).aestronglyMeasurable.prodMk
            hHν.aestronglyMeasurable))
    · -- Domination for `s > 0`: on `B_S(y)`,
      -- `|φ(‖x − y‖/s) (x − y)·H(x)| ≤ K ‖x − y‖ ‖H x‖ ≤ K S ‖H x‖`.
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [ae_restrict_iff' measurableSet_closedBall]
      refine Eventually.of_forall fun x hx => ?_
      rw [mem_closedBall, dist_eq_norm] at hx
      calc ‖φ (‖x - y‖ / s) * inner ℝ (x - y) (H x)‖
          = ‖φ (‖x - y‖ / s)‖ * ‖inner ℝ (x - y) (H x)‖ := norm_mul _ _
        _ ≤ K * (‖x - y‖ * ‖H x‖) :=
            mul_le_mul (hφK _ (div_nonneg (norm_nonneg _) (le_of_lt hs)))
              (norm_inner_le_norm _ _) (norm_nonneg _) hK0
        _ ≤ K * (S * ‖H x‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) hK0
        _ = K * S * ‖H x‖ := (mul_assoc _ _ _).symm
    · -- Pointwise continuity in `s` at `t ≠ 0`, since `φ` is continuous.
      refine Eventually.of_forall fun x => ?_
      exact (hφc.continuousAt.comp (continuousAt_const.div continuousAt_id ht.ne')).mul
        continuousAt_const
  -- Step 4: both functions agree on the neighbourhood `(0, S/T)` of `t`.
  exact hmain.congr (Filter.eventually_of_mem (Ioo_mem_nhds ht htR) hconv)

/-- Simon Ch. 4, 3.4–3.5 and 4.3–4.4, for one fixed cutoff `φ` (`C¹`, nonincreasing, `φ = 0` on
`[T, ∞)`): if the radial inequality (R) holds on `(0, S/T)` and `|a(t)| ≤ M t^{−β}` with `β < 1`, where
`I(t) = ∫ φ(|x − y|/t) dμ` and `a = (L/t^{n+1})/(1 + I/tⁿ)` with `L(t) = ∫ φ(|x − y|/t)(x − y)·H dμ`,
then `a` is continuous on `(0, S/T)` and `Ψ(ρ) = exp(−∫₀^ρ a)(1 + I(ρ)/ρⁿ)` is nondecreasing there. -/
theorem ted_lpm_fixed_cutoff_monotone : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (φ : ℝ → ℝ) (I a : ℝ → ℝ) (T S M β : ℝ), 0 < T → β < 1 → μ (closedBall y S) < ⊤ → IntegrableOn H (closedBall y S) μ → ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, T ≤ t → φ t = 0) → (∀ ρ : ℝ, 0 < ρ → T * ρ < S → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → (∀ t : ℝ, I t = ∫ x, φ (‖x - y‖ / t) ∂μ) → (∀ t : ℝ, a t = (∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → T * t < S → |a t| ≤ M * t ^ (-β)) → ContinuousOn a (Ioo 0 (S / T)) ∧ MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n)) (Ioo 0 (S / T)) := by
  intro n ℓ μ H y φ I a T S M β hT hβ hμS hH hφ hanti hφT hR hI ha hab
  -- `t < S/T` means `T t < S`
  have hTt : ∀ t, t < S / T → T * t < S := fun t htR => (lt_div_iff₀' hT).mp htR
  -- the pairing `L`, the derivative `P = I'` and the defect `Q = (t P − n I − L)/t`
  set L : ℝ → ℝ := fun s => ∫ x, φ (‖x - y‖ / s) * inner ℝ (x - y) (H x) ∂μ
  set P : ℝ → ℝ := fun t => -(∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ) / t with hP
  set Q : ℝ → ℝ := fun t => (t * P t - n * I t - L t) / t with hQ
  -- `φ ≥ 0` (it is nonincreasing and `φ(T) = 0`), hence `I ≥ 0`
  have hφnn : ∀ u, 0 ≤ φ u := fun u => by
    rcases le_total u T with h | h
    · simpa [hφT T le_rfl] using hanti h
    · exact le_of_eq (hφT u h).symm
  have hInn : ∀ t, 0 ≤ I t := fun t => by
    rw [hI t]
    exact integral_nonneg fun x => hφnn _
  -- the cutoff mass `I` is differentiable with `I' = P`, and the pairing `L` is continuous
  have hmass : ∀ t, 0 < t → t < S / T →
      Integrable (fun x => φ (‖x - y‖ / t)) μ ∧
        Integrable (fun x => ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) μ ∧
        HasDerivAt (fun s => ∫ x, φ (‖x - y‖ / s) ∂μ) (P t) t := fun t ht htR =>
    Submission.ted_lpm_fcm_cutoff_mass_hasDerivAt n ℓ μ y φ S T t hT hμS hφ hφT ht (hTt t htR)
  have hIder : ∀ t, 0 < t → t < S / T → HasDerivAt I (P t) t := fun t ht htR => by
    rw [show I = fun s => ∫ x, φ (‖x - y‖ / s) ∂μ from funext hI]
    exact (hmass t ht htR).2.2
  have hLc : ∀ t, 0 < t → t < S / T → ContinuousAt L t := fun t ht htR =>
    Submission.ted_lpm_fcm_cutoff_pairing_continuousAt n ℓ μ H y φ S T t hT hH hφ.continuous hφT
      ht (hTt t htR)
  -- the radial inequality (R) reads `n I − t I' ≤ −L`, i.e. `Q ≥ 0`
  have hQnn : ∀ t, 0 < t → t < S / T → 0 ≤ Q t := fun t ht htR => by
    obtain ⟨h1, h2, -⟩ := hmass t ht htR
    have hRt : ∫ x, ((n : ℝ) * φ (‖x - y‖ / t) + ‖x - y‖ / t * deriv φ (‖x - y‖ / t)) ∂μ ≤
        -L t := hR t ht (hTt t htR)
    rw [integral_add (h1.const_mul (n : ℝ)) h2, integral_const_mul, ← hI t] at hRt
    have htP : t * P t = -∫ x, ‖x - y‖ / t * deriv φ (‖x - y‖ / t) ∂μ := by
      simp only [hP]
      field_simp
    simp only [hQ]
    refine div_nonneg ?_ ht.le
    rw [htP]
    linarith
  have hid : ∀ t, 0 < t → t < S / T → (n : ℝ) * I t - t * P t + t * Q t = -L t :=
    fun t ht _ => by
      have ht0 : t ≠ 0 := ht.ne'
      simp only [hQ]
      field_simp
      ring
  -- the integrating factor: `Ψ' = exp(−∫₀ᵗ a) Q(t)/tⁿ` on `(0, S/T)`
  obtain ⟨hΨ, -⟩ := aal_cfs_integrating_factor_deriv n I L a P Q (S / T) M β hβ hIder hLc
    (fun t _ _ => hInn t) hid (fun t _ _ => ha t) (fun t ht htR => hab t ht (hTt t htR))
  refine ⟨fun t ht => ?_, ?_⟩
  · -- `a = (L/t^{n+1})/(1 + I/tⁿ)` is continuous at every point of `(0, S/T)`
    have hden : 1 + I t / t ^ n ≠ 0 := by
      have := div_nonneg (hInn t) (pow_pos ht.1 n).le
      linarith
    rw [show a = fun s => L s / s ^ (n + 1) / (1 + I s / s ^ n) from funext ha]
    exact (((hLc t ht.1 ht.2).div (continuous_pow (n + 1)).continuousAt
      (pow_ne_zero _ ht.1.ne')).div (continuousAt_const.add ((hIder t ht.1 ht.2).continuousAt.div
        (continuous_pow n).continuousAt (pow_ne_zero _ ht.1.ne'))) hden).continuousWithinAt
  · -- `Ψ' ≥ 0` on the open interval `(0, S/T)`
    refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 (S / T))
      (fun t ht => (hΨ t ht.1 ht.2).continuousAt.continuousWithinAt) ?_ ?_ <;> rw [interior_Ioo]
    · exact fun t ht => (hΨ t ht.1 ht.2).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hΨ t ht.1 ht.2).deriv]
      exact mul_nonneg (Real.exp_pos _).le (div_nonneg (hQnn t ht.1 ht.2) (pow_pos ht.1 n).le)

/-- **Simon Ch. 4, 4.1–4.8** (monotonicity with an `Lᵖ` mean-curvature term, `p > n`), for an
abstract measure `μ` satisfying the radial first-variation inequality (A5) on `B_S(y)`.  With
`α = 1 − n/p` and the smallness `(R^{p−n} ∫_{B_R(y)} |H|ᵖ dμ)^{1/p} ≤ (p − n)/(4p) Λ`, there is `F`
with `e^{−Λ} ≤ F ≤ e^Λ`, `|F(r) − 1| ≤ ½ e^{Λ/2} Λ (r/R)^α` (`≤ Λ (r/R)^α` if `Λ ≤ 1`) on `(0, R]`,
and `r ↦ F(r) μ(B_r(y))/rⁿ + (F(r) − 1)` nondecreasing on `(0, R]`.
Proof: cutoffs `φ_k → 1_{(-∞, 1]}` (`ted_lpm_am_cutoff_sequence`); the Hölder step
(`ted_lpm_curvature_holder`) and `ted_lpm_am_coefficient_bound` give `|a_k(t)| ≤ M t^{−n/p}` for the
coefficients `a_k(t) = L_k(t)/t^{n+1}/(1 + I_k(t)/tⁿ)`, and `ted_lpm_fixed_cutoff_monotone` makes
`exp(−∫₀^ρ a_k)(1 + I_k(ρ)/ρⁿ)` nondecreasing on `(0, R]`.  Dominated convergence
(`ted_lpm_am_cutoff_integral_tendsto`) gives `a_k → a₀` pointwise, Hölder with the indicator of
`B_t(y)` gives `|a₀(t)| ≤ (∫_{B_R(y)} |H|ᵖ dμ)^{1/p} t^{−n/p}`, and
`ted_lpm_am_integrating_factor_limit` passes to the limit for `F(r) = exp(−∫₀^r a₀)`. -/
theorem ted_lpm_abstract_monotonicity : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (R S Λ : ℝ), 0 < R → R < S → 0 < Λ → μ (closedBall y S) < ⊤ → IntegrableOn H (closedBall y S) μ → ∫⁻ x in closedBall y S, ‖H x‖ₑ ^ p ∂μ < ⊤ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → (∀ (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → T * ρ < S → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → ∃ F : ℝ → ℝ, (∀ r : ℝ, 0 < r → r ≤ R → Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (r / R) ^ (1 - (n : ℝ) / p) ∧ (Λ ≤ 1 → |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p))) ∧ ∀ s r : ℝ, 0 < s → s ≤ r → r ≤ R → F s * ((μ (closedBall y s)).toReal / s ^ n) + (F s - 1) ≤ F r * ((μ (closedBall y r)).toReal / r ^ n) + (F r - 1) := by
  intro n ℓ hn p hnp μ H y R S Λ hR hRS hΛ hμS hH hHpS hsmall hrad
  -- Exponents: `p > 1`, `β = n/p < 1`, `α = 1 - β > 0` and `κ Λ ≥ 0` with `κ = (p - n)/(4p)`.
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hβ1 : (n : ℝ) / p < 1 := (div_lt_one hp0).mpr hnp
  have hβpos : 0 < 1 - (n : ℝ) / p := by linarith
  have hκ : 0 ≤ (p - n) / (4 * p) * Λ :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) hΛ.le
  -- Step 1: `J(t) = ∫⁻_{B_t(y)} |H|ᵖ ≤ J(S) < ∞` for `t ≤ S`, and `N(t) = J(t).toReal ^ (1/p)` is
  -- nondecreasing on `(-∞, S]`.
  have hJt : ∀ t, t ≤ S → (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ) < ⊤ := fun t htS =>
    lt_of_le_of_lt (lintegral_mono_set (closedBall_subset_closedBall htS)) hHpS
  have hNmono : ∀ t t', t ≤ t' → t' ≤ S →
      (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤
        (∫⁻ x in closedBall y t', ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) := by
    intro t t' htt' ht'S
    exact Real.rpow_le_rpow ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (hJt t' ht'S).ne
        (lintegral_mono_set (closedBall_subset_closedBall htt'))) (by positivity)
  -- Step 2: with `K = N(R)`, the smallness hypothesis reads `K R^α ≤ κ Λ`, i.e.
  -- `K R^{1-β}/(1-β) ≤ Λ/4`.
  obtain ⟨J, hJ⟩ : ∃ J : ℝ≥0∞, J = ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ := ⟨_, rfl⟩
  have hJne : J ≠ ⊤ := by
    rw [hJ]
    exact (hJt R hRS.le).ne
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) :=
    ⟨_, rfl⟩
  have hKR : K * R ^ (1 - (n : ℝ) / p) ≤ (p - n) / (4 * p) * Λ := by
    have hRp : 0 < R ^ (p - n) := Real.rpow_pos_of_pos hR _
    have hp1' : 0 < 1 / p := by positivity
    have h := hsmall
    rw [← hJ] at h
    have hJ' : J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJne).symm
    rw [hJ', ← ENNReal.ofReal_mul hRp.le,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hRp.le ENNReal.toReal_nonneg) hp1'.le,
      ENNReal.ofReal_le_ofReal_iff hκ] at h
    rw [Real.mul_rpow hRp.le ENNReal.toReal_nonneg, ← Real.rpow_mul hR.le] at h
    have he : (p - n) * (1 / p) = 1 - (n : ℝ) / p := by
      field_simp
    rw [he] at h
    rw [hKdef, ← hJ]
    linarith
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hKR' : K * R ^ (1 - (n : ℝ) / p) / (1 - (n : ℝ) / p) ≤ Λ / 4 := by
    rw [div_le_iff₀ hβpos]
    calc K * R ^ (1 - (n : ℝ) / p) ≤ (p - n) / (4 * p) * Λ := hKR
      _ = Λ / 4 * (1 - (n : ℝ) / p) := by
          field_simp
  obtain ⟨KS, hKSdef⟩ : ∃ KS : ℝ,
      KS = (∫⁻ x in closedBall y S, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) := ⟨_, rfl⟩
  have hKS0 : 0 ≤ KS := by
    rw [hKSdef]
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hμsub : ∀ t, t ≤ S → μ (closedBall y t) < ⊤ := fun t htS =>
    lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall htS)) hμS
  have hHsub : ∀ t, t ≤ S → IntegrableOn H (closedBall y t) μ := fun t htS =>
    hH.mono_set (closedBall_subset_closedBall htS)
  -- Step 4: the cutoffs `φ k`, with `ε₁ = (S - R)/(2R)`, so that `(1 + ε k) R ≤ (1 + ε₁) R < S`.
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = (S - R) / (2 * R) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]
    exact div_pos (by linarith) (by linarith)
  have hε₁R : (1 + ε₁) * R < S := by
    have h : (1 + ε₁) * R = (R + S) / 2 := by
      rw [hε₁def]
      field_simp
      ring
    rw [h]
    linarith
  obtain ⟨φ, ε, hε, -, hφC, hφanti, hφ01, hφone, hφzero, hφev⟩ :=
    ted_lpm_am_cutoff_sequence ε₁ hε₁pos
  have hφc : ∀ k, Continuous (φ k) := fun k => (hφC k).continuous
  have hφzero₁ : ∀ k s, 1 + ε₁ ≤ s → φ k s = 0 := fun k s hs =>
    hφzero k s (le_trans (by linarith [(hε k).2]) hs)
  have hεR : ∀ k, (1 + ε k) * R < S := fun k =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith [(hε k).2]) hR.le) hε₁R
  -- Step 5: the cutoff quantities `I k t`, `L k t` and the coefficients `a k t`.
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ → ℝ, ∀ k t, I k t = ∫ x, φ k (‖x - y‖ / t) ∂μ :=
    ⟨fun k t => ∫ x, φ k (‖x - y‖ / t) ∂μ, fun _ _ => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℕ → ℝ → ℝ,
      ∀ k t, L k t = ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ :=
    ⟨fun k t => ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ, fun _ _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ → ℝ, ∀ k t, a k t = L k t / t ^ (n + 1) / (1 + I k t / t ^ n) :=
    ⟨fun k t => L k t / t ^ (n + 1) / (1 + I k t / t ^ n), fun _ _ => rfl⟩
  have hInn : ∀ k t, 0 ≤ I k t := fun k t => by
    rw [hI]
    exact integral_nonneg fun x => (hφ01 k _).1
  -- Step 6: Hölder at radius `(1 + ε k) t` and the coefficient bound give
  -- `|a k t| ≤ M t^{-β}` with `M = (1 + ε₁) N(S)`, uniformly in `k`.
  have hab : ∀ k t, 0 < t → (1 + ε k) * t < S →
      |a k t| ≤ (1 + ε₁) * KS * t ^ (-((n : ℝ) / p)) := by
    intro k t ht htS
    have hεk := hε k
    have ht' : 0 ≤ (1 + ε k) * t := by
      have : 0 < 1 + ε k := by linarith
      positivity
    have hhol := ted_lpm_curvature_holder n ℓ p hp1 μ H
      (fun x => φ k (‖x - y‖ / t)) y ((1 + ε k) * t) ht' (hμsub _ htS.le) (hHsub _ htS.le)
      (hJt _ htS.le)
      ((hφc k).comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
      (fun x => hφ01 k _) (fun x hx => hφzero k _ (by
        rw [le_div_iff₀ ht]
        exact hx.le))
    have hN : (∫⁻ x in closedBall y ((1 + ε k) * t), ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤ KS := by
      rw [hKSdef]
      exact hNmono _ S htS.le le_rfl
    have hNn : 0 ≤ (∫⁻ x in closedBall y ((1 + ε k) * t), ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hIp : 0 ≤ I k t ^ (1 - 1 / p) := Real.rpow_nonneg (hInn k t) _
    have hLb : |L k t| ≤ t * ((1 + ε₁) * KS) * I k t ^ (1 - 1 / p) := by
      rw [hL]
      rw [← hI] at hhol
      refine hhol.trans ?_
      apply mul_le_mul_of_nonneg_right _ hIp
      have h2 : 1 + ε k ≤ 1 + ε₁ := by linarith
      have h3 := mul_le_mul h2 hN hNn (by linarith)
      nlinarith
    rw [ha]
    exact Submission.ted_lpm_am_coefficient_bound n p t ((1 + ε₁) * KS) (I k t) (L k t) hp1 ht
      (by positivity) (hInn k t) hLb
  -- Step 7: for each `k`, `a k` is continuous and `Ψ_k(ρ) = exp(-∫₀^ρ a k)(1 + I k ρ/ρⁿ)` is
  -- nondecreasing on `(0, S/(1 + ε k)) ⊇ (0, R]`.
  have hfix : ∀ k, ContinuousOn (a k) (Ioo 0 (S / (1 + ε k))) ∧
      MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n))
        (Ioo 0 (S / (1 + ε k))) := fun k =>
    Submission.ted_lpm_fixed_cutoff_monotone n ℓ μ H y (φ k) (I k) (a k) (1 + ε k) S
      ((1 + ε₁) * KS) ((n : ℝ) / p) (by linarith [(hε k).1]) hβ1 hμS hH (hφC k) (hφanti k)
      (hφzero k)
      (fun ρ hρ hρS => hrad (φ k) (1 + ε k) ρ (hφC k) (hφanti k) (hφone k) (hφzero k) hρ hρS)
      (hI k) (fun t => by rw [ha, hL]) (hab k)
  have hsub : ∀ k, Ioc (0 : ℝ) R ⊆ Ioo 0 (S / (1 + ε k)) := by
    intro k t ht
    have h1 : 0 < 1 + ε k := by linarith [(hε k).1]
    refine ⟨ht.1, ?_⟩
    rw [lt_div_iff₀ h1]
    have := mul_le_mul_of_nonneg_left ht.2 h1.le
    nlinarith [hεR k]
  have hameas : ∀ k, AEStronglyMeasurable (a k) (volume.restrict (Ioc 0 R)) := fun k =>
    ((hfix k).1.mono (hsub k)).aestronglyMeasurable measurableSet_Ioc
  have hmono : ∀ k s r, 0 < s → s ≤ r → r ≤ R →
      Real.exp (-∫ t in (0)..s, a k t) * (1 + I k s / s ^ n) ≤
        Real.exp (-∫ t in (0)..r, a k t) * (1 + I k r / r ^ n) := by
    intro k s r hs hsr hrR
    exact (hfix k).2 (hsub k ⟨hs, hsr.trans hrR⟩) (hsub k ⟨hs.trans_le hsr, hrR⟩) hsr
  have hab' : ∀ k t, 0 < t → t ≤ R → |a k t| ≤ (1 + ε₁) * KS * t ^ (-((n : ℝ) / p)) := by
    intro k t ht htR
    exact hab k t ht (lt_of_le_of_lt (mul_le_mul_of_nonneg_left htR (by linarith [(hε k).1]))
      (hεR k))
  -- Step 8: dominated convergence on `B_S(y)` gives `I k t → μ(B_t(y))`,
  -- `L k t → ∫_{B_t(y)} (x - y)·H` and hence `a k t → a₀ t` for `t ∈ (0, R]`.
  have hgint : IntegrableOn (fun x => inner ℝ (x - y) (H x)) (closedBall y S) μ := by
    refine Integrable.mono' (hH.norm.const_mul S) ?_ ?_
    · exact continuous_inner.comp_aestronglyMeasurable
        ((by fun_prop : Continuous fun x : Amb n ℓ => x - y).aestronglyMeasurable.prodMk
          hH.aestronglyMeasurable)
    · rw [ae_restrict_iff' measurableSet_closedBall]
      refine Eventually.of_forall fun x hx => ?_
      have hxS : ‖x - y‖ ≤ S := by simpa [mem_closedBall, dist_eq_norm] using hx
      calc ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ ‖x - y‖ * ‖H x‖ := norm_inner_le_norm _ _
        _ ≤ S * ‖H x‖ := mul_le_mul_of_nonneg_right hxS (norm_nonneg _)
  have h1int : IntegrableOn (fun _ => (1 : ℝ)) (closedBall y S) μ :=
    integrableOn_const hμS.ne
  have hIlim : ∀ t, 0 < t → t ≤ R →
      Tendsto (fun k => I k t) atTop (𝓝 ((μ (closedBall y t)).toReal)) := by
    intro t ht htR
    have h := Submission.ted_lpm_am_cutoff_integral_tendsto n ℓ μ (fun _ => (1 : ℝ)) y φ S
      (1 + ε₁) t ht (by linarith)
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left htR (by linarith)) hε₁R).le
      h1int hφc hφ01 hφone hφzero₁ hφev
    simp only [mul_one] at h
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real_def] at h
    exact h.congr fun k => (hI k t).symm
  have hLlim : ∀ t, 0 < t → t ≤ R →
      Tendsto (fun k => L k t) atTop (𝓝 (∫ x in closedBall y t, inner ℝ (x - y) (H x) ∂μ)) := by
    intro t ht htR
    have h := Submission.ted_lpm_am_cutoff_integral_tendsto n ℓ μ
      (fun x => inner ℝ (x - y) (H x)) y φ S (1 + ε₁) t ht (by linarith)
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left htR (by linarith)) hε₁R).le
      hgint hφc hφ01 hφone hφzero₁ hφev
    exact h.congr fun k => (hL k t).symm
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ → ℝ, ∀ t, a₀ t =
      (∫ x in closedBall y t, inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) /
        (1 + (μ (closedBall y t)).toReal / t ^ n) := ⟨_, fun _ => rfl⟩
  have halim : ∀ t, 0 < t → t ≤ R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t)) := by
    intro t ht htR
    have hden : 1 + (μ (closedBall y t)).toReal / t ^ n ≠ 0 := by
      have := div_nonneg (ENNReal.toReal_nonneg (a := μ (closedBall y t))) (pow_pos ht n).le
      linarith
    rw [ha₀]
    have h := ((hLlim t ht htR).div_const (t ^ (n + 1))).div
      (tendsto_const_nhds.add ((hIlim t ht htR).div_const (t ^ n))) hden
    exact h.congr fun k => (ha k t).symm
  -- Step 9: Hölder with the indicator of `B_t(y)` and the coefficient bound give
  -- `|a₀ t| ≤ K t^{-β}` for `t ∈ (0, R]`.
  have ha₀b : ∀ t, 0 < t → t ≤ R → |a₀ t| ≤ K * t ^ (-((n : ℝ) / p)) := by
    intro t ht htR
    have htS : t ≤ S := by linarith
    have hhol := ted_lpm_curvature_holder n ℓ p hp1 μ H
      ((closedBall y t).indicator (fun _ => (1 : ℝ))) y t ht.le (hμsub t htS) (hHsub t htS)
      (hJt t htS) (aestronglyMeasurable_const.indicator measurableSet_closedBall)
      (fun x => by
        by_cases hx : x ∈ closedBall y t
        · simp [hx]
        · simp [hx])
      (fun x hx => by
        have : x ∉ closedBall y t := by
          simpa [mem_closedBall, dist_eq_norm, not_le] using hx
        simp [this])
    have e1 : ∫ x, (closedBall y t).indicator (fun _ => (1 : ℝ)) x * inner ℝ (x - y) (H x) ∂μ =
        ∫ x in closedBall y t, inner ℝ (x - y) (H x) ∂μ := by
      rw [← integral_indicator measurableSet_closedBall]
      congr 1
      funext x
      by_cases hx : x ∈ closedBall y t
      · simp [hx]
      · simp [hx]
    have e2 : ∫ x, (closedBall y t).indicator (fun _ => (1 : ℝ)) x ∂μ =
        (μ (closedBall y t)).toReal := by
      rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul, mul_one,
        Measure.real_def]
    rw [e1, e2] at hhol
    have hN : (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤ K := by
      rw [hKdef]
      exact hNmono t R htR hRS.le
    have hLb : |∫ x in closedBall y t, inner ℝ (x - y) (H x) ∂μ| ≤
        t * K * (μ (closedBall y t)).toReal ^ (1 - 1 / p) := by
      refine hhol.trans ?_
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      exact mul_le_mul_of_nonneg_left hN ht.le
    rw [ha₀]
    exact Submission.ted_lpm_am_coefficient_bound n p t K _ _ hp1 ht hK0 ENNReal.toReal_nonneg hLb
  -- Steps 10-12: pass to the limit `k → ∞` with `F(r) = exp(-∫₀^r a₀)`; then
  -- `F(t)(1 + μ(B_t(y))/tⁿ) = F(t) μ(B_t(y))/tⁿ + (F(t) - 1) + 1` gives (ii).
  have hQlim : ∀ t, 0 < t → t ≤ R → Tendsto (fun k => 1 + I k t / t ^ n) atTop
      (𝓝 (1 + (μ (closedBall y t)).toReal / t ^ n)) := fun t ht htR =>
    tendsto_const_nhds.add ((hIlim t ht htR).div_const _)
  obtain ⟨hi, hii⟩ := Submission.ted_lpm_am_integrating_factor_limit R ((n : ℝ) / p)
    ((1 + ε₁) * KS) K Λ a a₀ (fun k t => 1 + I k t / t ^ n)
    (fun t => 1 + (μ (closedBall y t)).toReal / t ^ n)
    hR hβ1 hΛ hKR' hameas hab' halim ha₀b hQlim hmono
  refine ⟨fun r => Real.exp (-∫ t in (0)..r, a₀ t), hi, ?_⟩
  intro s r hs hsr hrR
  have h := hii s r hs hsr hrR
  simp only at h ⊢
  linarith [h, show Real.exp (-∫ t in (0)..s, a₀ t) * (1 + (μ (closedBall y s)).toReal / s ^ n) =
      Real.exp (-∫ t in (0)..s, a₀ t) * ((μ (closedBall y s)).toReal / s ^ n) +
        (Real.exp (-∫ t in (0)..s, a₀ t) - 1) + 1 by ring,
    show Real.exp (-∫ t in (0)..r, a₀ t) * (1 + (μ (closedBall y r)).toReal / r ^ n) =
      Real.exp (-∫ t in (0)..r, a₀ t) * ((μ (closedBall y r)).toReal / r ^ n) +
        (Real.exp (-∫ t in (0)..r, a₀ t) - 1) + 1 by ring]
/-- **Blow-up change of variables** (Simon Ch. 3, Remark 1.8(2)).  For `η = η_{x,r}`,
`η(z) = r⁻¹(z − x)`, with `r > 0`, any set `M` and any `f, θ`:
`∫_{η(M)} f(y) θ(x + r y) dHⁿ(y) = r⁻ⁿ ∫_M f(η z) θ(z) dHⁿ(z)`.  As `η` is a homeomorphism and
`Hⁿ(η(S)) = r⁻ⁿ Hⁿ(S)` for every `S`, `Hⁿ ⌞ η(M) = r⁻ⁿ η_#(Hⁿ ⌞ M)`; no integrability is needed. -/
theorem rsod_blowUp_setIntegral_eq : ∀ (n ℓ : ℕ) (M : Set (Amb n ℓ)) (f θ : Amb n ℓ → ℝ) (x : Amb n ℓ) (r : ℝ), 0 < r → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ)) = (r ^ n)⁻¹ * ∫ z in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * θ z ∂(μHE[n] : Measure (Amb n ℓ)) := by
  intro n ℓ M f θ x r hr
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  set η := Poincare.SimonGMT.Chapter03.blowUpMap x r with hη
  -- `η` is the homeomorphism `z ↦ r⁻¹ • (z - x)`, hence a measurable embedding.
  let e : Amb n ℓ ≃ₜ Amb n ℓ :=
    (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : ⇑e = η := rfl
  have hemb : MeasurableEmbedding η := he ▸ e.toMeasurableEquiv.measurableEmbedding
  have hinj : Function.Injective η := he ▸ e.injective
  have hsurj : Function.Surjective η := he ▸ e.surjective
  -- `Hⁿ(η(S)) = (r⁻¹)ⁿ Hⁿ(S)` for every set `S`: a translation followed by a homothety.
  have hscale : ∀ S : Set (Amb n ℓ), μ (η '' S) = ENNReal.ofReal r⁻¹ ^ n * μ S := by
    intro S
    have hshift : Isometry (fun y : Amb n ℓ => y - x) :=
      Isometry.of_dist_eq fun a b => by simp only [dist_eq_norm, sub_sub_sub_cancel_right]
    have himage : η '' S = AffineMap.homothety (0 : Amb n ℓ) r⁻¹ '' ((fun y => y - x) '' S) := by
      rw [← image_comp]
      congr 1
      funext y
      simp [hη, Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Amb n ℓ) (inv_ne_zero hr.ne'),
      hshift.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow,
      ← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (inv_pos.mpr hr).le]
  -- `Hⁿ ⌞ η(M) = (r⁻¹)ⁿ η_#(Hⁿ ⌞ M)`, checked on measurable `A` via `A ∩ η(M) = η(η⁻¹(A) ∩ M)`.
  have hmeas : μ.restrict (η '' M) = (ENNReal.ofReal r⁻¹ ^ n) • (μ.restrict M).map η := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply hemb.measurable hA,
      Measure.restrict_apply (hemb.measurable hA), smul_eq_mul, ← hscale, image_inter hinj,
      image_preimage_eq A hsurj]
  -- Transfer the integral and simplify `x + r • η z = z`.
  rw [hmeas, integral_smul_measure, hemb.integral_map, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (inv_pos.mpr hr).le, inv_pow, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hη, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne',
    one_smul, add_sub_cancel]
/-- **Simon Ch. 1, Theorem 3.6 (Upper Density Theorem)** in the contract normalization: for a
`ν`-null-measurable `A` with `ν A < ∞`, the upper density `Θ*ⁿ(ν, A, x)` vanishes for
`Hⁿ`-a.e. `x ∉ A`.  Simon's printed proof: on the level set `S_t = {x ∉ A : Θ*ⁿ > t}` and for
closed `C ⊆ A`, Vitali's covering lemma gives the comparison bound 3.3 for `ν ⌞ (A \ C)` (with
the non-sharp constant `8ⁿ / ω_n`, enough for null sets); `ν (A \ C)` is small by 1.15(2).  The
levels `t = 1/(k+1)` exhaust `Θ*ⁿ ≠ 0`, and `μHE[n]` is a multiple of `μH[n]`. -/
theorem upperDensity_ne_zero_outside_hausdorff_null : ∀ {n ℓ : ℕ} (ν : Measure (Amb n ℓ)) (A : Set (Amb n ℓ)), NullMeasurableSet A ν → ν A < ∞ → (μHE[n] : Measure (Amb n ℓ)) {x | x ∉ A ∧ limsup (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) ≠ 0} = 0 := by
  intro n ℓ ν A hA hAfin
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  -- Simon 1.15(2): `A` contains closed sets `C` with `ν (A \ C)` arbitrarily small.
  have hreg : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ C ⊆ A, IsClosed C ∧ ν (A \ C) < ε := by
    intro ε hε
    obtain ⟨A', hA'A, hA'm, hA'eq⟩ := hA.exists_measurable_subset_ae_eq
    have : IsFiniteMeasure (ν.restrict A') :=
      isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top hAfin.ne (measure_mono hA'A))
    obtain ⟨C, hCA', hC, hCε⟩ :=
      hA'm.exists_isClosed_sdiff_lt (μ := ν.restrict A') (measure_ne_top _ _) hε
    refine ⟨C, hCA'.trans hA'A, hC, ?_⟩
    rw [Measure.restrict_apply (hA'm.diff hC.measurableSet), inter_eq_left.2 sdiff_subset] at hCε
    rwa [measure_congr (hA'eq.symm.diff (EventuallyEq.refl _ C))]
  -- The level set `S_t` is `μH[n]`-null for every `t > 0`.
  have hlevel : ∀ t : ℝ, 0 < t → μH[(n : ℝ)] {x : Amb n ℓ | x ∉ A ∧ ENNReal.ofReal t <
      limsup (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
        (𝓝[>] 0)} = 0 := by
    intro t ht
    set S := {x : Amb n ℓ | x ∉ A ∧ ENNReal.ofReal t <
      limsup (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
        (𝓝[>] 0)} with hS
    have hKnn : (0 : ℝ) ≤ 8 ^ n / unitBallVolume n / t :=
      div_nonneg (div_nonneg (by positivity) hω.le) ht.le
    set K : ℝ≥0∞ := ENNReal.ofReal (8 ^ n / unitBallVolume n / t) with hK
    -- Simon 3.3 for `ν ⌞ (A \ C)`, `C ⊆ A` closed, via Vitali's covering lemma.
    have hcomp : ∀ C ⊆ A, IsClosed C → μH[(n : ℝ)] S ≤ K * ν (A \ C) := by
      intro C hCA hC
      have hcov : ∀ R : ℝ, 0 < R → ∃ u : Set (Amb n ℓ × ℝ), u.Countable ∧
          u.PairwiseDisjoint (fun b => closedBall b.1 b.2) ∧
          (∀ b ∈ u, 0 < b.2 ∧ b.2 ≤ R ∧
            ENNReal.ofReal t * ENNReal.ofReal (unitBallVolume n * b.2 ^ n) ≤
              ν.restrict (A \ C) (closedBall b.1 b.2)) ∧
          S ⊆ ⋃ b ∈ u, closedBall b.1 (4 * b.2) := by
        intro R hR
        obtain ⟨u, huT, hud, hucov⟩ :=
          Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
            {b : Amb n ℓ × ℝ | b.1 ∈ S ∧ 0 < b.2 ∧ b.2 ≤ R ∧
              ENNReal.ofReal t * ENNReal.ofReal (unitBallVolume n * b.2 ^ n) ≤
                ν.restrict (A \ C) (closedBall b.1 b.2)}
            Prod.fst Prod.snd R (fun b hb => hb.2.2.1) 4 (by norm_num)
        refine ⟨u, hud.countable_of_nonempty_interior fun b hb =>
          ⟨b.1, ball_subset_interior_closedBall (mem_ball_self (huT hb).2.1)⟩, hud,
          fun b hb => (huT hb).2, fun x hx => ?_⟩
        -- A small ball around `x ∉ C` on which the density quotient exceeds `t`.
        obtain ⟨ρ, hρ, hρC⟩ := nhds_basis_closedBall.mem_iff.1
          (hC.isOpen_compl.mem_nhds fun h => hx.1 (hCA h))
        obtain ⟨r, hr, hrI⟩ := ((frequently_lt_of_lt_limsup (by isBoundedDefault) hx.2).and_eventually
          (Ioo_mem_nhdsGT (lt_min hR hρ))).exists
        have hr0 : 0 < r := hrI.1
        have hmass : ENNReal.ofReal t * ENNReal.ofReal (unitBallVolume n * r ^ n) ≤
            ν.restrict (A \ C) (closedBall x r) := by
          rw [Measure.restrict_apply measurableSet_closedBall]
          have hset : closedBall x r ∩ (A \ C) = A ∩ closedBall x r := by
            ext y
            constructor
            · rintro ⟨hy1, hy2, -⟩
              exact ⟨hy2, hy1⟩
            · rintro ⟨hy1, hy2⟩
              exact ⟨hy2, hy1,
                hρC (closedBall_subset_closedBall (hrI.2.le.trans (min_le_right _ _)) hy2)⟩
          rw [hset]
          exact ((ENNReal.lt_div_iff_mul_lt
            (Or.inl (ENNReal.ofReal_pos.2 (mul_pos hω (pow_pos hr0 n))).ne')
            (Or.inl ENNReal.ofReal_ne_top)).1 hr).le
        obtain ⟨b, hbu, hsub⟩ := hucov (x, r) ⟨hx, hr0, hrI.2.le.trans (min_le_left _ _), hmass⟩
        exact mem_biUnion hbu (hsub (mem_closedBall_self hr0.le))
      -- Covers by the enlarged balls at scales `1/(k+1) → 0`.
      choose u hu using fun k : ℕ => hcov (1 / ((k : ℝ) + 1)) (by positivity)
      have : ∀ k, Countable (u k) := fun k => (hu k).1.to_subtype
      have hH := Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) S (l := atTop)
        (fun k : ℕ => ENNReal.ofReal (8 * (1 / ((k : ℝ) + 1))))
        (by simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 8))
        (fun k (b : u k) => closedBall (b : Amb n ℓ × ℝ).1 (4 * (b : Amb n ℓ × ℝ).2))
        (Eventually.of_forall fun k b => ediam_le_of_forall_dist_le fun y hy z hz => by
          have h1 := dist_triangle_right y z (b : Amb n ℓ × ℝ).1
          have h2 := ((hu k).2.2.1 b b.2).2.1
          rw [mem_closedBall] at hy hz
          linarith)
        (Eventually.of_forall fun k x hx => by
          obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.1 ((hu k).2.2.2 hx)
          exact mem_iUnion.2 ⟨⟨b, hb⟩, hxb⟩)
      refine hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_))
      calc ∑' b : u k, ediam (closedBall (b : Amb n ℓ × ℝ).1 (4 * (b : Amb n ℓ × ℝ).2)) ^ (n : ℝ)
          ≤ ∑' b : u k,
              K * ν.restrict (A \ C) (closedBall (b : Amb n ℓ × ℝ).1 (b : Amb n ℓ × ℝ).2) := by
            refine ENNReal.tsum_le_tsum fun b => ?_
            obtain ⟨hb0, -, hbm⟩ := (hu k).2.2.1 b b.2
            calc ediam (closedBall (b : Amb n ℓ × ℝ).1 (4 * (b : Amb n ℓ × ℝ).2)) ^ (n : ℝ)
                ≤ ENNReal.ofReal (8 * (b : Amb n ℓ × ℝ).2) ^ (n : ℝ) := by
                  gcongr
                  exact ediam_le_of_forall_dist_le fun y hy z hz => by
                    have h1 := dist_triangle_right y z (b : Amb n ℓ × ℝ).1
                    rw [mem_closedBall] at hy hz
                    linarith
              _ = K * (ENNReal.ofReal t *
                    ENNReal.ofReal (unitBallVolume n * (b : Amb n ℓ × ℝ).2 ^ n)) := by
                  rw [hK, ← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_mul hKnn,
                    ENNReal.rpow_natCast,
                    ← ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 8 * (b : Amb n ℓ × ℝ).2)]
                  congr 1
                  field_simp
                  ring
              _ ≤ K * ν.restrict (A \ C) (closedBall (b : Amb n ℓ × ℝ).1 (b : Amb n ℓ × ℝ).2) := by
                  gcongr
        _ = K * ν.restrict (A \ C) (⋃ b ∈ u k, closedBall b.1 b.2) := by
            rw [ENNReal.tsum_mul_left,
              measure_biUnion (hu k).1 (hu k).2.1 fun b _ => measurableSet_closedBall]
        _ ≤ K * ν (A \ C) := by
            refine mul_le_mul_right ?_ K
            exact (measure_mono (subset_univ _)).trans_eq (Measure.restrict_apply_univ _)
    -- Letting `ν (A \ C) → 0`.
    have hKtop : K ≠ ∞ := ENNReal.ofReal_ne_top
    refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun c hc => ?_) bot_le
    obtain ⟨ε, hε0, hεc⟩ := ENNReal.exists_nnreal_pos_mul_lt hKtop hc.ne'
    obtain ⟨C, hCA, hC, hCε⟩ := hreg ε (by exact_mod_cast hε0.ne')
    calc μH[(n : ℝ)] S ≤ K * ν (A \ C) := hcomp C hCA hC
      _ ≤ K * ε := by gcongr
      _ = ε * K := mul_comm _ _
      _ ≤ c := hεc.le
  -- The levels `t = 1/(k+1)` exhaust the positive upper densities.
  have hE : μH[(n : ℝ)] {x : Amb n ℓ | x ∉ A ∧ limsup (fun r : ℝ => ν (A ∩ closedBall x r) /
      ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) ≠ 0} = 0 := by
    refine measure_mono_null (fun x hx => ?_)
      (measure_iUnion_null fun k : ℕ => hlevel (1 / ((k : ℝ) + 1)) (by positivity))
    obtain ⟨s, -, hs0, hs⟩ := ENNReal.lt_iff_exists_real_btwn.1 (pos_iff_ne_zero.2 hx.2)
    have hs0' : 0 < s := ENNReal.ofReal_pos.1 hs0
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hs0'
    exact mem_iUnion.2 ⟨k, hx.1, ((ENNReal.ofReal_lt_ofReal_iff hs0').2 hk).trans hs⟩
  -- `μHE[n]` is a scalar multiple of `μH[n]`.
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hE, smul_zero]
/-- Simon Ch. 3, Theorem 1.9 (measurability of `x ↦ p_{T_x M}`, used for Ch. 5, Lemma 2.1): for
injective `L : ℝⁿ → ℝ^{n+ℓ}` the orthogonal projection onto `L(ℝⁿ)` is `L (Lᵀ L)⁻¹ Lᵀ`, hence it
depends continuously on `L`.  Here `Lᵀ w = Σᵢ ⟨L eᵢ, w⟩ eᵢ` is the transpose, `Lᵀ L` is a unit of
`End(ℝⁿ)` because `⟨Lᵀ L v, v⟩ = |L v|²`, inversion is continuous at units, and
`w − L (Lᵀ L)⁻¹ Lᵀ w ⊥ L(ℝⁿ)` identifies the formula with `p_{L(ℝⁿ)}`. -/
theorem aetp_starProjection_range_continuousOn : ∀ (n ℓ : ℕ), ContinuousOn (fun L : Rn n →L[ℝ] Amb n ℓ => (LinearMap.range L.toLinearMap).starProjection) {L : Rn n →L[ℝ] Amb n ℓ | Function.Injective L} := by
  intro n ℓ
  -- The transpose `T L = Lᵀ`, built from the standard basis `e i` of `ℝⁿ`.
  let e : Fin n → Rn n := fun i => EuclideanSpace.single i (1 : ℝ)
  let T : (Rn n →L[ℝ] Amb n ℓ) → (Amb n ℓ →L[ℝ] Rn n) :=
    fun L => ∑ i, (innerSL ℝ (L (e i))).smulRight (e i)
  have hT : ∀ L (w : Amb n ℓ) (v : Rn n), inner ℝ (T L w) v = inner ℝ w (L v) := by
    intro L w v
    have hv : v = ∑ i, v i • e i := by
      simpa [e] using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
    have hTw : T L w = ∑ i, inner ℝ (L (e i)) w • e i := by
      simp [T]
    rw [hTw]
    conv_rhs => rw [hv]
    simp only [sum_inner, inner_sum, map_sum, map_smul, real_inner_smul_left,
      real_inner_smul_right, e, EuclideanSpace.inner_single_left, one_mul, map_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm]
    ring
  have hTc : Continuous T := by
    refine continuous_finsetSum _ fun i _ => ?_
    have h1 : Continuous fun L : Rn n →L[ℝ] Amb n ℓ => innerSL ℝ (L (e i)) :=
      (innerSL ℝ).continuous.comp (continuous_id.clm_apply continuous_const)
    exact ((ContinuousLinearMap.smulRightL ℝ (Amb n ℓ) (Rn n)).continuous.comp h1).clm_apply
      continuous_const
  -- The Gram operator `A L = Lᵀ L` and the candidate projection `Q L = L (Lᵀ L)⁻¹ Lᵀ`.
  let A : (Rn n →L[ℝ] Amb n ℓ) → (Rn n →L[ℝ] Rn n) := fun L => (T L).comp L
  let Q : (Rn n →L[ℝ] Amb n ℓ) → (Amb n ℓ →L[ℝ] Amb n ℓ) :=
    fun L => L.comp ((Ring.inverse (A L)).comp (T L))
  -- `A L` is a unit for injective `L`: `A L v = 0` gives `|L v|² = ⟨A L v, v⟩ = 0`.
  have hA : ∀ L : Rn n →L[ℝ] Amb n ℓ, Function.Injective L → IsUnit (A L) := by
    intro L hL
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
      LinearMap.ker_eq_bot']
    intro v hv
    have h0 : T L (L v) = 0 := hv
    have h1 : inner ℝ (L v) (L v) = 0 := by
      rw [← hT, h0, inner_zero_left]
    exact hL (by rw [inner_self_eq_zero.mp h1, map_zero])
  -- `Q L = p_{L(ℝⁿ)}` for injective `L`: `Q L w ∈ L(ℝⁿ)` and `Lᵀ (w − Q L w) = 0`.
  have hQ : ∀ L : Rn n →L[ℝ] Amb n ℓ, Function.Injective L →
      (LinearMap.range L.toLinearMap).starProjection = Q L := by
    intro L hL
    ext1 w
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨_, rfl⟩
    · rintro _ ⟨v, rfl⟩
      have h1 : T L (L (Ring.inverse (A L) (T L w))) = T L w := by
        have h2 := congrArg (fun S : Rn n →L[ℝ] Rn n => S (T L w))
          (Ring.mul_inverse_cancel _ (hA L hL))
        simpa [A] using h2
      rw [inner_sub_left, ContinuousLinearMap.coe_coe, ← hT, ← hT]
      simp only [Q, ContinuousLinearMap.coe_comp, Function.comp_apply]
      rw [h1, sub_self]
  -- `Q` is continuous at every injective `L`, since inversion is continuous at units.
  have hQc : ∀ L : Rn n →L[ℝ] Amb n ℓ, Function.Injective L → ContinuousAt Q L := by
    intro L hL
    have hAc : Continuous A := hTc.clm_comp continuous_id
    obtain ⟨u, hu⟩ := hA L hL
    have hinv : ContinuousAt (fun L => Ring.inverse (A L)) L := by
      have h1 := NormedRing.inverse_continuousAt u
      rw [hu] at h1
      exact h1.comp hAc.continuousAt
    exact continuous_id.continuousAt.clm_comp (hinv.clm_comp hTc.continuousAt)
  intro L hL
  exact (hQc L hL).continuousWithinAt.congr (fun L' hL' => hQ L' hL') (hQ L hL)
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): the profile of the cutoff `ζ(x) = φ(|x − ξ|/ρ)` with
`ζ ≡ 1` in `B_{ρ/2}(ξ)`, `ζ ≡ 0` outside `B_ρ(ξ)` and `|∇ζ| ≤ 3/ρ`.  With `S = smoothTransition`,
the bump `g(t) = S(12(t − 1/2)) S(12(1 − t)) ∈ [0, 1]` vanishes for `t ≤ 1/2` and for `t ≥ 1` and
equals `1` on `[7/12, 11/12]`, so `c = ∫_{1/2}^1 g ≥ 1/3`; then `φ(t) = 1 − c⁻¹ ∫_{1/2}^t g` is
`C^∞` with `|φ'| = c⁻¹ g ≤ 3`. -/
theorem exists_smooth_step_profile_lipschitz_three : ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ t, t ≤ 1 / 2 → φ t = 1) ∧ (∀ t, 1 ≤ t → φ t = 0) ∧ LipschitzWith 3 φ := by
  -- The bump `g`: smooth, with values in `[0, 1]`, zero off `(1/2, 1)`, one on `[7/12, 11/12]`.
  set g : ℝ → ℝ := fun t =>
    Real.smoothTransition (12 * (t - 1 / 2)) * Real.smoothTransition (12 * (1 - t)) with hg_def
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    have h₁ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (t - 1 / 2) := by fun_prop
    have h₂ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (1 - t) := by fun_prop
    exact (Real.smoothTransition.contDiff.comp h₁).mul (Real.smoothTransition.contDiff.comp h₂)
  have hg_cont : Continuous g := hg_smooth.continuous
  have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hg_cont.intervalIntegrable a b
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t =>
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hg_le_one : ∀ t, g t ≤ 1 := fun t =>
    (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans
      (Real.smoothTransition.le_one _)
  have hg_left : ∀ t, t ≤ 1 / 2 → g t = 0 := fun t ht => by
    simp only [hg_def]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  have hg_right : ∀ t, 1 ≤ t → g t = 0 := fun t ht => by
    simp only [hg_def]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 12 * (1 - t) ≤ 0), mul_zero]
  have hg_mid : ∀ t, 7 / 12 ≤ t → t ≤ 11 / 12 → g t = 1 := fun t h₁ h₂ => by
    simp only [hg_def]
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith), mul_one]
  -- The normalizing constant `c = ∫_{1/2}^1 g ≥ ∫_{7/12}^{11/12} 1 = 1/3`, so `c⁻¹ ≤ 3`.
  set c : ℝ := ∫ s in (1 / 2 : ℝ)..1, g s with hc_def
  have hc_ge : 1 / 3 ≤ c := by
    have h : ∫ s in (7 / 12 : ℝ)..(11 / 12), g s = 1 / 3 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
      · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
        norm_num
      · intro s hs
        rw [uIcc_of_le (by norm_num)] at hs
        exact hg_mid s hs.1 hs.2
    rw [← h]
    exact intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
      (ae_of_all _ hg_nonneg) (hg_int _ _)
  have hc_pos : 0 < c := by linarith
  have hcinv_le : c⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ hc_pos (by norm_num)]
    linarith
  -- The primitive `F(t) = ∫_{1/2}^t g`: `F' = g` (FTC), so `F` is smooth; `0 ≤ F ≤ c`,
  -- `F = 0` on `(-∞, 1/2]` and `F = c` on `[1, ∞)`.
  set F : ℝ → ℝ := fun t => ∫ s in (1 / 2 : ℝ)..t, g s with hF_def
  have hF_deriv : ∀ t, HasDerivAt F (g t) t := fun t =>
    (hg_cont.integral_hasStrictDerivAt (1 / 2) t).hasDerivAt
  have hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F :=
    contDiff_infty_iff_deriv.2 ⟨fun t => (hF_deriv t).differentiableAt,
      (funext fun t => (hF_deriv t).deriv : deriv F = g) ▸ hg_smooth⟩
  have hF_left : ∀ t, t ≤ 1 / 2 → F t = 0 := fun t ht => by
    simp only [hF_def]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro s hs
      rw [uIcc_of_ge ht] at hs
      exact hg_left s hs.2
  have hF_right : ∀ t, 1 ≤ t → F t = c := fun t ht => by
    simp only [hF_def, hc_def]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hg_int (1 / 2) 1) (hg_int 1 t)]
    have h : ∫ s in (1 : ℝ)..t, g s = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [uIcc_of_le ht] at hs
        exact hg_right s hs.1
    rw [h, add_zero]
  have hF_bounds : ∀ t, 0 ≤ F t ∧ F t ≤ c := fun t => by
    rcases le_total t (1 / 2) with ht | ht
    · rw [hF_left t ht]
      exact ⟨le_rfl, hc_pos.le⟩
    rcases le_total 1 t with ht' | ht'
    · rw [hF_right t ht']
      exact ⟨hc_pos.le, le_rfl⟩
    exact ⟨intervalIntegral.integral_nonneg ht fun u _ => hg_nonneg u,
      intervalIntegral.integral_mono_interval le_rfl ht ht' (ae_of_all _ hg_nonneg) (hg_int _ _)⟩
  -- The profile `φ = 1 − c⁻¹ F`, with `φ' = −c⁻¹ g`.
  have hφ_deriv : ∀ t, HasDerivAt (fun t => 1 - c⁻¹ * F t) (-(c⁻¹ * g t)) t := fun t => by
    simpa using ((hF_deriv t).const_mul c⁻¹).const_sub 1
  refine ⟨fun t => 1 - c⁻¹ * F t, contDiff_const.sub (contDiff_const.mul hF_smooth), ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨h₀, h₁⟩ := hF_bounds t
    have hci : 0 ≤ c⁻¹ := inv_nonneg.2 hc_pos.le
    have h : c⁻¹ * F t ≤ 1 := by
      calc c⁻¹ * F t ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left h₁ hci
        _ = 1 := inv_mul_cancel₀ hc_pos.ne'
    exact ⟨by linarith, by linarith [mul_nonneg hci h₀]⟩
  · intro t ht
    simp only [hF_left t ht, mul_zero, sub_zero]
  · intro t ht
    simp only [hF_right t ht, inv_mul_cancel₀ hc_pos.ne', sub_self]
  · refine lipschitzWith_of_nnnorm_deriv_le (fun t => (hφ_deriv t).differentiableAt) fun t => ?_
    rw [(hφ_deriv t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (mul_nonneg (inv_nonneg.2 hc_pos.le) (hg_nonneg t))]
    calc c⁻¹ * g t ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left (hg_le_one t) (inv_nonneg.2 hc_pos.le)
      _ ≤ 3 := by rw [mul_one]; exact hcinv_le
      _ = ((3 : ℝ≥0) : ℝ) := by norm_num
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 107), smoothness of the cutoff: if `φ` is `C^∞` with
`φ ≡ 1` on `(-∞, 1/2]` and `ρ > 0`, then `ζ(x) = φ(‖x − ξ‖/ρ)` is `C^∞` on `ℝᵐ`.  Near `ξ`,
`ζ ≡ 1` on `B̆_{ρ/2}(ξ)`; at `x ≠ ξ` the norm is `C^∞` at `x − ξ ≠ 0`. -/
theorem contDiff_radial_profile_of_eq_one_le_half : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ) (φ : ℝ → ℝ), 0 < ρ → ContDiff ℝ (⊤ : ℕ∞) φ → (∀ t, t ≤ 1 / 2 → φ t = 1) → ContDiff ℝ (⊤ : ℕ∞) (fun x : Rn m => φ (‖x - ξ‖ / ρ)) := by
  intro m ξ ρ φ hρ hφ hφ1
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x ξ with rfl | hx
  · -- `ζ ≡ 1` on the open ball `B̆_{ρ/2}(ξ)`, a neighbourhood of `ξ`.
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds x (half_pos hρ)] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hφ1 _ ((div_le_iff₀ hρ).2 (by linarith))
  · -- `y ↦ ‖y − ξ‖/ρ` is `C^∞` at `x` since `x − ξ ≠ 0`; compose with `φ`.
    have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Rn m => ‖y - ξ‖ / ρ) x :=
      ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)).div_const ρ
    exact hφ.contDiffAt.comp x h
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): the cutoff gradient bound `|∇ζ| ≤ 3/ρ`, for a general
Lipschitz constant `K` in place of `3`.  If `φ` is `K`-Lipschitz and `ρ > 0`, then
`ζ(y) = φ(‖y - ξ‖/ρ)` is `(K/ρ)`-Lipschitz by the reverse triangle inequality, so
`‖Dζ(x)‖ ≤ K/ρ` at every `x` (where `ζ` is not differentiable, `fderiv ℝ ζ x = 0`). -/
theorem norm_fderiv_radial_profile_le_of_lipschitzWith : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ) (K : ℝ≥0) (φ : ℝ → ℝ), 0 < ρ → LipschitzWith K φ → ∀ x : Rn m, ‖fderiv ℝ (fun y : Rn m => φ (‖y - ξ‖ / ρ)) x‖ ≤ (K : ℝ) / ρ := by
  intro m ξ ρ K φ hρ hφ x
  -- `ζ(y) = φ(‖y - ξ‖/ρ)` is `(K/ρ)`-Lipschitz by the reverse triangle inequality.
  have hKρ : ((K / ρ.toNNReal : ℝ≥0) : ℝ) = K / ρ := by
    rw [NNReal.coe_div, Real.coe_toNNReal ρ hρ.le]
  have hlip : LipschitzWith (K / ρ.toNNReal) fun y : Rn m => φ (‖y - ξ‖ / ρ) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [hKρ]
    calc dist (φ (‖y - ξ‖ / ρ)) (φ (‖z - ξ‖ / ρ))
        ≤ K * dist (‖y - ξ‖ / ρ) (‖z - ξ‖ / ρ) := hφ.dist_le_mul _ _
      _ = K / ρ * |‖y - ξ‖ - ‖z - ξ‖| := by
          rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hρ]; ring
      _ ≤ K / ρ * ‖(y - ξ) - (z - ξ)‖ := by gcongr; exact abs_norm_sub_norm_le _ _
      _ = K / ρ * dist y z := by rw [sub_sub_sub_cancel_right, dist_eq_norm]
  -- A `C`-Lipschitz function has `‖Dζ(x)‖ ≤ C` (and `fderiv ℝ ζ x = 0` where not differentiable).
  exact (norm_fderiv_le_of_lipschitz ℝ hlip).trans_eq hKρ
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): a cutoff `ζ ∈ C^∞(ℝᵐ)` with `0 ≤ ζ ≤ 1`, `ζ ≡ 1` on
`B_{ρ/2}(ξ)`, `ζ ≡ 0` outside `B̆_ρ(ξ)` and `|Dζ| ≤ 3/ρ`.  Take `ζ(x) = φ(|x − ξ|/ρ)` for the smooth
`3`-Lipschitz step profile `φ` (`φ = 1` on `(-∞, 1/2]`, `φ = 0` on `[1, ∞)`): `ζ` is smooth since it
is constant near `ξ`, and the radial lift of a `3`-Lipschitz profile has `|Dζ| ≤ 3/ρ`. -/
theorem exists_smooth_cutoff_half_ball_grad_le : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ), 0 < ρ → ∃ ζ : Rn m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ Metric.closedBall ξ (ρ / 2), ζ x = 1) ∧ (∀ x, ρ ≤ dist x ξ → ζ x = 0) ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / ρ := by
  intro m ξ ρ hρ
  obtain ⟨φ, hφ_smooth, hφ_bounds, hφ_one, hφ_zero, hφ_lip⟩ :=
    Submission.exists_smooth_step_profile_lipschitz_three
  refine ⟨fun x => φ (‖x - ξ‖ / ρ),
    Submission.contDiff_radial_profile_of_eq_one_le_half m ξ ρ φ hρ hφ_smooth hφ_one,
    fun x => hφ_bounds _, fun x hx => hφ_one _ ?_, fun x hx => hφ_zero _ ?_, fun x => ?_⟩
  · -- `|x − ξ| ≤ ρ/2`, so `|x − ξ|/ρ ≤ 1/2`.
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [div_le_iff₀ hρ]
    linarith
  · -- `ρ ≤ |x − ξ|`, so `1 ≤ |x − ξ|/ρ`.
    rw [dist_eq_norm] at hx
    rw [le_div_iff₀ hρ]
    linarith
  · -- The profile is `3`-Lipschitz, so `|Dζ(x)| ≤ 3/ρ`.
    have h := Submission.norm_fderiv_radial_profile_le_of_lipschitzWith m ξ ρ 3 φ hρ hφ_lip x
    rwa [NNReal.coe_ofNat] at h
/-- **Density of the varifold weight with respect to `Hⁿ`** (Simon Ch. 4, 1.1: `μ_V = Hⁿ ⌞ θ`,
with `θ = 0` off `M`).  Writing `g = 1_M θ`: (i) `g` has a Borel representative that is `≥ 0`
everywhere; (ii) `∫_S φ dμ_V = ∫_S g φ dHⁿ` for every Borel `S` and every `φ ≥ 0` (not necessarily
measurable).  `g ≥ 0` because `θ > 0` on `M`, and `g` is `Hⁿ`-a.e. measurable since `M` is
`Hⁿ`-null-measurable and `θ` is a.e. measurable on `M`; `max(mk g, 0)` is the representative.
For (ii), `μ_V⌞S = ((Hⁿ⌞M)⌞S) ⌞ ofReal ∘ θ`, the finite density can be multiplied in without
measurability of `φ`, `(Hⁿ⌞M)⌞S = (Hⁿ⌞S)⌞M`, and integrating over `M` is integrating `1_M`. -/
theorem gwe_vgt_weight_density : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), (∃ g : Amb n ℓ → ℝ, Measurable g ∧ (∀ y, 0 ≤ g y) ∧ g =ᵐ[(μHE[n] : Measure (Amb n ℓ))] V.carrier.indicator V.mult) ∧ ∀ S : Set (Amb n ℓ), MeasurableSet S → ∀ φ : Amb n ℓ → ℝ≥0∞, ∫⁻ y in S, φ y ∂V.weight = ∫⁻ y in S, ENNReal.ofReal (V.carrier.indicator V.mult y) * φ y ∂(μHE[n] : Measure (Amb n ℓ)) := by
  intro n ℓ U V
  have hM : NullMeasurableSet V.carrier (μHE[n] : Measure (Amb n ℓ)) :=
    V.nullMeasurableSet_carrier
  -- `g = 1_M θ ≥ 0` everywhere, since `θ > 0` on `M`.
  have hg0 : ∀ y, 0 ≤ V.carrier.indicator V.mult y := by
    intro y
    by_cases hy : y ∈ V.carrier
    · rw [indicator_of_mem hy]
      exact (V.mult_pos y hy).le
    · rw [indicator_of_notMem hy]
  refine ⟨?_, ?_⟩
  · -- (i) `g` is `Hⁿ`-a.e. measurable; `max(mk g, 0)` is a nonnegative Borel representative.
    have hae : AEMeasurable (V.carrier.indicator V.mult) (μHE[n] : Measure (Amb n ℓ)) :=
      (aemeasurable_indicator_iff₀ hM).2 V.aemeasurable_mult
    refine ⟨fun y => max (hae.mk _ y) 0, hae.measurable_mk.max measurable_const,
      fun y => le_max_right _ _, ?_⟩
    filter_upwards [hae.ae_eq_mk] with y hy
    rw [← hy]
    exact max_eq_left (hg0 y)
  · -- (ii) Remove the finite density `ofReal ∘ θ`, then rearrange the restrictions.
    intro S hS φ
    have hρ : AEMeasurable (fun x => ENNReal.ofReal (V.mult x))
        (((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).restrict S) :=
      V.aemeasurable_mult.ennreal_ofReal.restrict
    have hMS : NullMeasurableSet V.carrier ((μHE[n] : Measure (Amb n ℓ)).restrict S) :=
      hM.mono Measure.restrict_le_self
    rw [RectifiableVarifold.weight, restrict_withDensity hS,
      lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hρ
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
      Measure.restrict_restrict hS, inter_comm, ← Measure.restrict_restrict₀ hMS,
      ← lintegral_indicator₀ hMS]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ V.carrier
    · simp [indicator_of_mem hy]
    · simp [indicator_of_notMem hy]
/-- **Measurability of the graph map and of the graph Jacobian** over a closed ball `B = B_R(0)`.
Let `F(x) = q(graphPoint x (f x))` with `f` continuous on `B`, and `J_f(x) =
√det(Iₙ + (⟨Df(x) e_a, Df(x) e_b⟩)_{a,b})`.  (i) `F(A)` is Borel for every Borel `A ⊆ B`:
`(a, b) ↦ graphPoint a b` is continuous coordinatewise, so `F` is continuous on `B`; `F` is
injective, since the first `n` coordinates of `F(x)` determine `x` after undoing `q`; apply
Lusin–Souslin.  (ii) `F` agrees on `B` with the Borel map `B.piecewise F 0` (`B` closed).
(iii) `J_f = Φ ∘ Df` with `Φ` continuous on `ℝⁿ →L[ℝ] ℝ^ℓ` and `Df` Borel. -/
theorem gwe_vgt_graph_measurability : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ), ContinuousOn f (closedBall 0 R) → (∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → MeasurableSet (q '' graphOver f A)) ∧ (∃ Fh : Rn n → Amb n ℓ, Measurable Fh ∧ ∀ x ∈ closedBall (0 : Rn n) R, Fh x = q (graphPoint x (f x))) ∧ Measurable (fun x : Rn n => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ)))))) := by
  intro n ℓ q f R hf
  -- `(a, b) ↦ graphPoint a b` is continuous: each coordinate is a coordinate of `a` or of `b`.
  have hgp : Continuous (fun p : Rn n × Rn ℓ => graphPoint p.1 p.2) := by
    unfold graphPoint
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp only [Fin.append_left]
      exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)
    · simp only [Fin.append_right]
      exact (continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp continuous_snd)
  -- `F = q ∘ (x ↦ graphPoint x (f x))` is continuous on `B` and injective.
  have hFc : ContinuousOn (fun x => q (graphPoint x (f x))) (closedBall 0 R) :=
    q.continuous.comp_continuousOn (hgp.comp_continuousOn (continuousOn_id.prodMk hf))
  have hFi : Function.Injective (fun x => q (graphPoint x (f x))) := by
    intro x y hxy
    have h := congrArg (fun (z : Amb n ℓ) (j : Fin n) => z (Fin.castAdd ℓ j)) (q.injective hxy)
    ext j
    simpa [graphPoint] using congrFun h j
  refine ⟨fun A hA hAB => ?_, ?_, ?_⟩
  · -- (i) Lusin–Souslin for the continuous injective map `F` on the Borel set `A`.
    rw [graphOver, image_image]
    exact hA.image_of_continuousOn_injOn (hFc.mono hAB) hFi.injOn
  · -- (ii) `B.piecewise F 0` is Borel and equals `F` on `B`.
    classical
    exact ⟨(closedBall 0 R).piecewise (fun x => q (graphPoint x (f x))) fun _ => 0,
      hFc.measurable_piecewise continuousOn_const measurableSet_closedBall,
      fun x hx => piecewise_eq_of_mem _ _ _ hx⟩
  · -- (iii) `J_f = Φ ∘ fderiv ℝ f` with `Φ` continuous and `fderiv ℝ f` Borel.
    have hΦ : Continuous fun D : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det
        ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
          inner ℝ (D (EuclideanSpace.single a (1 : ℝ)))
            (D (EuclideanSpace.single b (1 : ℝ))))) := by
      refine Real.continuous_sqrt.comp (Continuous.matrix_det (continuous_const.add
        (continuous_matrix fun a b => ?_)))
      simp only [Matrix.of_apply]
      exact (continuous_eval_const _).inner (continuous_eval_const _)
    exact hΦ.measurable.comp (measurable_fderiv ℝ f)

end Submission
/-- **Bochner and null-set transfer** (steps 5 and 6 of the varifold graph transfer).  The
`lintegral` transfer identity says `μ ⌞ S = G_#((Lⁿ ⌞ A) ⌞ W)`; pushing Bochner integrals through
`G` and the density `W ≥ 0` gives (i) for every Borel `φ`, and testing it on `φ = 1_{Z'}` for a Borel
`μ`-null `Z' ⊇ Z` gives `W = 0` a.e. on `A ∩ G⁻¹(Z)`. -/
theorem Submission.gwe_vgt_transfer_consequences : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (S : Set (Amb n ℓ)) (A : Set (Rn n)) (G : Rn n → Amb n ℓ) (W : Rn n → ℝ), MeasurableSet A → Measurable G → Measurable W → (∀ x, 0 ≤ W x) → (∀ φ : Amb n ℓ → ℝ≥0∞, Measurable φ → ∫⁻ y in S, φ y ∂μ = ∫⁻ x in A, ENNReal.ofReal (W x) * φ (G x)) → (∀ φ : Amb n ℓ → ℝ, Measurable φ → ∫ y in S, φ y ∂μ = ∫ x in A, W x * φ (G x)) ∧ ∀ Z : Set (Amb n ℓ), μ Z = 0 → ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ A → G x ∈ Z → W x = 0 := by
  intro n ℓ μ S A G W hA hG hW hW0 hT
  -- Step 1: `μ ⌞ S = G_# ν` with `ν = (Lⁿ ⌞ A).withDensity (ofReal ∘ W)`, tested on Borel `T`.
  have hpush : μ.restrict S =
      Measure.map G ((volume.restrict A).withDensity fun x => ENNReal.ofReal (W x)) := by
    ext T hTm
    calc μ.restrict S T = ∫⁻ y in S, T.indicator 1 y ∂μ := (lintegral_indicator_one hTm).symm
      _ = ∫⁻ x in A, ENNReal.ofReal (W x) * T.indicator 1 (G x) :=
          hT _ (measurable_one.indicator hTm)
      _ = ∫⁻ x in A, (G ⁻¹' T).indicator (fun x => ENNReal.ofReal (W x)) x := by
          refine lintegral_congr fun x => ?_
          by_cases hx : G x ∈ T <;> simp [hx]
      _ = ∫⁻ x in G ⁻¹' T, ENNReal.ofReal (W x) ∂(volume.restrict A) :=
          lintegral_indicator (hG hTm) _
      _ = Measure.map G ((volume.restrict A).withDensity fun x => ENNReal.ofReal (W x)) T := by
          rw [Measure.map_apply hG hTm, withDensity_apply _ (hG hTm)]
  refine ⟨fun φ hφ => ?_, fun Z hZ => ?_⟩
  · -- Step 2: push the Bochner integral through `G`, then through the density `ofReal ∘ W`.
    rw [hpush, integral_map hG.aemeasurable hφ.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hW.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hW0 x), smul_eq_mul]
  · -- Steps 3–5: test the identity on `1_{Z'}` for a Borel `μ`-null `Z' ⊇ Z`.
    obtain ⟨Z', hZZ', hZ'm, hZ'0⟩ := exists_measurable_superset_of_null hZ
    have hmeas : Measurable fun x => ENNReal.ofReal (W x) * Z'.indicator 1 (G x) :=
      hW.ennreal_ofReal.mul ((measurable_one.indicator hZ'm).comp hG)
    have h0 : ∫⁻ x in A, ENNReal.ofReal (W x) * Z'.indicator 1 (G x) = 0 := by
      rw [← hT _ (measurable_one.indicator hZ'm), lintegral_indicator_one hZ'm]
      exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hZ'0.le)
    filter_upwards [(ae_restrict_iff' hA).1 ((lintegral_eq_zero_iff hmeas).1 h0)]
      with x hx hxA hGx
    have h1 := hx hxA
    simp only [Set.indicator_of_mem (hZZ' hGx), Pi.one_apply, mul_one, Pi.zero_apply,
      ENNReal.ofReal_eq_zero] at h1
    exact le_antisymm h1 (hW0 x)

namespace Submission

/-- **The Gram matrix of a linear map** (Simon Ch. 5, proof of Theorem 4.5, p. 119: the graph
Jacobian `J_F = √det(δ_ij + D_i f · D_j f)`).  For `D : ℝⁿ →L[ℝ] ℝ^ℓ` let `G_ab = ⟨D e_a, D e_b⟩`.
Then (i) `G` is symmetric, since the real inner product is; (ii) `G` is positive semidefinite:
`x · Gx = Σ_{a,b} x_a x_b ⟨D e_a, D e_b⟩ = |Σ_a x_a D e_a|² ≥ 0` by bilinearity; and
(iii) `trace G = Σ_a |D e_a|² = |D|²` (`hsNormSq`). -/
theorem gwe_gjb_gram_symm_psd_trace : ∀ (n ℓ : ℕ) (D : Rn n →L[ℝ] Rn ℓ), Matrix.IsSymm (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) ∧ (∀ x : Fin n → ℝ, 0 ≤ dotProduct x (Matrix.mulVec (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) x)) ∧ Matrix.trace (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) = hsNormSq D := by
  intro n ℓ D
  refine ⟨?_, fun x => ?_, ?_⟩
  · -- (i) `G_ba = ⟨D e_b, D e_a⟩ = ⟨D e_a, D e_b⟩ = G_ab`.
    refine Matrix.IsSymm.ext fun a b => ?_
    simp only [Matrix.of_apply]
    exact real_inner_comm _ _
  · -- (ii) `x · Gx = ⟨w, w⟩` for `w = Σ_a x_a • D e_a`, by bilinearity.
    have h : dotProduct x (Matrix.mulVec (Matrix.of fun a b : Fin n =>
        inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) x) =
        inner ℝ (∑ a, x a • D (EuclideanSpace.single a (1 : ℝ)))
          (∑ b, x b • D (EuclideanSpace.single b (1 : ℝ))) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, sum_inner, inner_sum,
        real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [real_inner_comm (D (EuclideanSpace.single a (1 : ℝ)))]
      ring
    rw [h]
    exact real_inner_self_nonneg
  · -- (iii) `trace G = Σ_a ⟨D e_a, D e_a⟩ = Σ_a ‖D e_a‖² = hsNormSq D`.
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, hsNormSq, real_inner_self_eq_norm_sq]
/-- **Determinant bounds for `I + G`** (graph Jacobian bounds in the tilt-excess decay argument):
if `G` is a symmetric real `n × n` matrix with `0 ≤ x ⬝ᵥ G x` for all `x`, then
`1 ≤ det (I + G) ≤ exp (trace G)`.  By Gaussian elimination: `A = I + G` satisfies
`x ⬝ᵥ x ≤ x ⬝ᵥ A x`, so its pivot `a = A₀₀` is at least `1`, and clearing the first column gives
`det A = a * det S` for the Schur complement `S = C - a⁻¹ b bᵀ`.  `S` is again symmetric with
`x ⬝ᵥ x ≤ x ⬝ᵥ S x` (test `A` on `(-(b ⬝ᵥ x) / a, x)`) and `trace S ≤ trace A - a`, so induction
gives `1 ≤ det A ≤ exp (trace A - n)` using `a ≤ exp (a - 1)`; finally `trace (I + G) = n + trace G`.
-/
theorem gwe_gjb_det_one_add_bounds : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℝ), Matrix.IsSymm G → (∀ x : Fin n → ℝ, 0 ≤ dotProduct x (Matrix.mulVec G x)) → 1 ≤ Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + G) ∧ Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + G) ≤ Real.exp (Matrix.trace G) := by
  -- Induction on the size: a symmetric `A` with `x ⬝ᵥ x ≤ x ⬝ᵥ A x` for all `x` satisfies
  -- `1 ≤ det A ≤ exp (trace A - m)`.
  have key : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ), (∀ i j, A j i = A i j) →
      (∀ x : Fin m → ℝ, dotProduct x x ≤ dotProduct x (Matrix.mulVec A x)) →
      1 ≤ A.det ∧ A.det ≤ Real.exp (A.trace - m) := by
    intro m
    induction m with
    | zero =>
      intro A _ _
      simp [Matrix.det_fin_zero, Matrix.trace]
    | succ m ih =>
      intro A hA hq
      -- The pivot `a = A₀₀ = e₀ ⬝ᵥ A e₀` is at least `e₀ ⬝ᵥ e₀ = 1`.
      have ha : 1 ≤ A 0 0 := by
        have h := hq (Pi.single 0 1)
        simpa using h
      have ha0 : A 0 0 ≠ 0 := (by linarith : (0 : ℝ) < A 0 0).ne'
      -- The Schur complement `S = C - a⁻¹ b bᵀ` of the pivot.
      obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin m) (Fin m) ℝ,
          S = Matrix.of fun i j => A i.succ j.succ - A i.succ 0 / A 0 0 * A 0 j.succ := ⟨_, rfl⟩
      have hSs : ∀ i j, S j i = S i j := by
        intro i j
        rw [hS, Matrix.of_apply, Matrix.of_apply, hA i.succ j.succ, hA 0 i.succ, hA 0 j.succ]
        ring
      -- `x ⬝ᵥ S x = y ⬝ᵥ A y` for `y = (-(b ⬝ᵥ x) / a, x)`, and `y ⬝ᵥ y ≥ x ⬝ᵥ x`.
      have hSq : ∀ x : Fin m → ℝ, dotProduct x x ≤ dotProduct x (Matrix.mulVec S x) := by
        intro x
        obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ∑ j : Fin m, A 0 j.succ * x j := ⟨_, rfl⟩
        obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑ i : Fin m, x i * ∑ j : Fin m, A i.succ j.succ * x j :=
          ⟨_, rfl⟩
        have hrow : ∀ i : Fin m,
            Matrix.mulVec S x i = ∑ j, A i.succ j.succ * x j - A 0 i.succ / A 0 0 * b := by
          intro i
          simp only [Matrix.mulVec, dotProduct, hS, Matrix.of_apply]
          rw [hb, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hA 0 i.succ]
          ring
        have eS : dotProduct x (Matrix.mulVec S x) = Q - b * b / A 0 0 := by
          calc dotProduct x (Matrix.mulVec S x)
              = ∑ i, (x i * ∑ j, A i.succ j.succ * x j - A 0 i.succ * x i * (b / A 0 0)) := by
                simp only [dotProduct]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [hrow i]
                ring
            _ = Q - b * b / A 0 0 := by
                rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hQ, ← hb]
                ring
        have eA : ∀ t : ℝ, dotProduct (Fin.cons t x : Fin (m + 1) → ℝ)
            (Matrix.mulVec A (Fin.cons t x)) = A 0 0 * t * t + 2 * t * b + Q := by
          intro t
          simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
          have h1 : ∑ i : Fin m, x i * (A i.succ 0 * t + ∑ j, A i.succ j.succ * x j) =
              t * b + Q := by
            rw [hb, hQ, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hA 0 i.succ]
            ring
          rw [h1, ← hb]
          ring
        have eI : ∀ t : ℝ, dotProduct (Fin.cons t x : Fin (m + 1) → ℝ) (Fin.cons t x) =
            t * t + dotProduct x x := by
          intro t
          simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        have h := hq (Fin.cons (-b / A 0 0) x)
        rw [eA, eI] at h
        rw [eS]
        have e : A 0 0 * (-b / A 0 0) * (-b / A 0 0) + 2 * (-b / A 0 0) * b + Q =
            Q - b * b / A 0 0 := by
          field_simp
          ring
        nlinarith [mul_self_nonneg (-b / A 0 0)]
      -- Eliminating the first column below the pivot: `det A = a * det S`.
      have hdet : A.det = A 0 0 * S.det := by
        obtain ⟨c, hc⟩ : ∃ c : Fin (m + 1) → ℝ,
            c = Fin.cons 0 (fun i : Fin m => A i.succ 0 / A 0 0) := ⟨_, rfl⟩
        obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
            E = Matrix.of fun i j => A i j - c i * A 0 j := ⟨_, rfl⟩
        have hc0 : c 0 = 0 := by rw [hc]; rfl
        have hE0 : ∀ j, E 0 j = A 0 j := by
          intro j
          rw [hE, Matrix.of_apply, hc0]
          ring
        have hAE : A.det = E.det :=
          Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 hc0 fun i j => by
            rw [hE0, hE, Matrix.of_apply]
            ring
        have hcol : ∀ i : Fin m, E i.succ 0 = 0 := by
          intro i
          rw [hE, Matrix.of_apply, hc, Fin.cons_succ, div_mul_cancel₀ _ ha0, sub_self]
        have hsub : E.submatrix Fin.succ Fin.succ = S := by
          ext i j
          simp only [Matrix.submatrix_apply, hE, hS, Matrix.of_apply, hc, Fin.cons_succ]
        rw [hAE, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
        simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero,
          pow_zero, one_mul, Fin.succAbove_zero, hE0, hsub]
      -- `trace A = a + trace S + Σᵢ bᵢ² / a`.
      have htr : A.trace = A 0 0 + S.trace + ∑ i : Fin m, A 0 i.succ ^ 2 / A 0 0 := by
        simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, hS, Matrix.of_apply]
        rw [Finset.sum_sub_distrib]
        have e : ∀ i : Fin m, A i.succ 0 / A 0 0 * A 0 i.succ = A 0 i.succ ^ 2 / A 0 0 := by
          intro i
          rw [hA 0 i.succ]
          ring
        simp only [e]
        ring
      obtain ⟨h1, h2⟩ := ih S hSs hSq
      have hsum : 0 ≤ ∑ i : Fin m, A 0 i.succ ^ 2 / A 0 0 :=
        Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (by linarith)
      have hexp : A 0 0 ≤ Real.exp (A 0 0 - 1) := by
        have := Real.add_one_le_exp (A 0 0 - 1)
        linarith
      refine ⟨?_, ?_⟩
      · rw [hdet]
        nlinarith
      · rw [hdet]
        calc A 0 0 * S.det ≤ Real.exp (A 0 0 - 1) * Real.exp (S.trace - m) :=
              mul_le_mul hexp h2 (by linarith) (Real.exp_pos _).le
          _ = Real.exp (A 0 0 - 1 + (S.trace - m)) := (Real.exp_add _ _).symm
          _ ≤ Real.exp (A.trace - ↑(m + 1)) := by
              apply Real.exp_le_exp.mpr
              rw [htr]
              push_cast
              linarith
  intro n G hG hpos
  have hsymm : ∀ i j, ((1 : Matrix (Fin n) (Fin n) ℝ) + G) j i =
      ((1 : Matrix (Fin n) (Fin n) ℝ) + G) i j :=
    (Matrix.isSymm_one.add hG).apply
  have hquad : ∀ x : Fin n → ℝ,
      dotProduct x x ≤ dotProduct x (Matrix.mulVec ((1 : Matrix (Fin n) (Fin n) ℝ) + G) x) := by
    intro x
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
    linarith [hpos x]
  obtain ⟨h1, h2⟩ := key n _ hsymm hquad
  refine ⟨h1, h2.trans_eq ?_⟩
  rw [Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]
  congr 1
  ring
/-- **Scalar exponential bound** for the area Jacobian of a linear graph (used with `s = |D|²`,
`T = n` in `J(D) ≤ exp(|D|²/2) ≤ 1 + (e^{n/2}/2)|D|²`): for `0 ≤ s ≤ T`,
`exp(s/2) ≤ 1 + (exp(T/2)/2) s`.  With `t = s/2`, `1 - t ≤ exp(-t)` (`add_one_le_exp` at `-t`)
times `exp t > 0` gives `exp t ≤ 1 + t exp t`, and `t exp t ≤ t exp(T/2)` by monotonicity of
`exp` and `0 ≤ t ≤ T/2`. -/
theorem gwe_gjb_exp_half_le : ∀ (s T : ℝ), 0 ≤ s → s ≤ T → Real.exp (s / 2) ≤ 1 + Real.exp (T / 2) / 2 * s := by
  intro s T hs hsT
  -- `1 - s/2 ≤ exp (-(s/2))`: `add_one_le_exp` at `-(s/2)`.
  have h1 : 1 - s / 2 ≤ Real.exp (-(s / 2)) := by
    linarith [Real.add_one_le_exp (-(s / 2))]
  -- Multiply by `exp (s/2) > 0`, using `exp (-(s/2)) * exp (s/2) = exp 0 = 1`.
  have h2 : (1 - s / 2) * Real.exp (s / 2) ≤ 1 := by
    calc (1 - s / 2) * Real.exp (s / 2) ≤ Real.exp (-(s / 2)) * Real.exp (s / 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  -- `exp` is monotone, `s/2 ≤ T/2` and `0 ≤ s/2`.
  have h4 : s / 2 * Real.exp (s / 2) ≤ s / 2 * Real.exp (T / 2) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by linarith)
  -- `exp (s/2) ≤ 1 + (s/2) exp (s/2) ≤ 1 + (s/2) exp (T/2)`.
  linarith
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

set_option maxHeartbeats 10000000 in
open scoped CompactlySupported in
/-- **Simon Ch. 3, 1.6–1.9 and Rem. 1.8, with the Lipschitz-graph form of Ch. 3, 1.9** for a
rectifiable varifold `V = v(M, θ)` in `U`, `μ = μ_V`: (0) the weighted approximate tangent plane
exists `μ`-a.e.; (1) `p_x = V.tangentProj x` is `μ`-a.e. the projection onto an `n`-plane; (2)
`x ↦ p_x` is `μ`-a.e. strongly measurable; (3) `Θⁿ(μ, x) = θ(x)` `μ`-a.e.; (4) on a rotated
Lipschitz graph `x = q(x', f(x'))`, `p_x` is `μ`-a.e. the projection onto
`q(graph Df(x'))` wherever `f` is differentiable.  Proof: `M` is covered, up to an `Hⁿ`-null set,
by compact Lusin pieces `K` of `θ` (Simon 1.17, proved inline) intersected with images `S = F(A)`
of bounded Borel pieces on which a Lipschitz chart `F` approximates an injective linear map
(`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`), hence is bi-Lipschitz; a rotated
Lipschitz graph `w ↦ q(w, f̃(w))` (`f̃` a Lipschitz extension of `f`) is globally bi-Lipschitz.
The injective Lipschitz area formula `Hⁿ ⌞ F(A) = F_#(J_F 𝓛ⁿ ⌞ A)`, Lebesgue points of `1_A J_F`
and the derivative of `F` give the blow-up of `Hⁿ ⌞ S` (limit `Hⁿ ⌞ DF(a)(ℝⁿ)`); the blow-up
identity `rsod_blowUp_setIntegral_eq`, the upper density theorem
`upperDensity_ne_zero_outside_hausdorff_null` (for `μ ⌞ (M \ K)`, `Hⁿ ⌞ (K \ S)`, `Hⁿ ⌞ (S \ K)`)
and continuity of `θ` on `K` give the weighted plane, unique as `θ > 0`; squeezing with cutoffs
gives the density, and `p_{range L} = L (L* L)⁻¹ L*` with a Borel inverse of `F` on `A` gives
measurability. -/
theorem ted_tangent_plane_facts : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ V : RectifiableVarifold n ℓ U, (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P) ∧ (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) ∧ AEStronglyMeasurable V.tangentProj V.weight ∧ (∀ᵐ x ∂V.weight, V.HasDensity x (V.mult x)) ∧ ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ) (L : ℝ≥0), LipschitzOnWith L f (closedBall 0 R) → ∀ᵐ x ∂V.weight, ∀ x' ∈ ball (0 : Rn n) R, x = q (graphPoint x' (f x')) → DifferentiableAt ℝ f x' → V.tangentProj x = (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (fderiv ℝ f x' v)))).starProjection := by
  intro n ℓ hn U hU V
  -- Simon Ch. 3, Remark 1.8(1): Lusin exhaustion of the carrier by compact pieces on which `θ`
  -- is continuous (Lusin's theorem, Simon 1.17, proved inline).
  have lusin_exhaustion : ∃ K : ℕ → Set (Amb n ℓ), (∀ m, IsCompact (K m)) ∧ (∀ m, K m ⊆ V.carrier) ∧ (∀ m, ContinuousOn V.mult (K m)) ∧ (∀ m, (μHE[n] : Measure (Amb n ℓ)) (K m) < ⊤) ∧ (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ ⋃ m, K m) = 0 := by
    -- A Borel representative `f` of `θ`.
    set f : Amb n ℓ → ℝ := V.aemeasurable_mult.mk V.mult
    have hfm : Measurable f := V.aemeasurable_mult.measurable_mk
    have hfae : V.mult =ᵐ[(μHE[n] : Measure (Amb n ℓ)).restrict V.carrier] f :=
      V.aemeasurable_mult.ae_eq_mk
    -- A Borel `G ⊆ M` of full `Hⁿ`-measure in `M` on which `θ = f`.
    obtain ⟨M₁, hM₁M, hM₁m, hM₁ae⟩ := V.nullMeasurableSet_carrier.exists_measurable_subset_ae_eq
    obtain ⟨T, hTsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 hfae)
    rw [Measure.restrict_apply hTm] at hT0
    set G : Set (Amb n ℓ) := M₁ \ T
    have hGm : MeasurableSet G := hM₁m.diff hTm
    have hGM : G ⊆ V.carrier := sdiff_subset.trans hM₁M
    have hGf : ∀ x ∈ G, V.mult x = f x := fun x hx => by_contra fun h => hx.2 (hTsub h)
    have hMG : (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ G) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (measure_union_null (ae_eq_set.1 hM₁ae).2 hT0)
      by_cases hx₁ : x ∈ M₁
      · exact Or.inr ⟨by_contra fun h => hx.2 ⟨hx₁, h⟩, hx.1⟩
      · exact Or.inl ⟨hx.1, hx₁⟩
    -- Compact exhaustion `Q i` of `U`.
    set Q : ℕ → Set (Amb n ℓ) :=
      fun i => closedBall 0 (i : ℝ) ∩ {x | (i : ℝ≥0∞)⁻¹ ≤ infEDist x Uᶜ}
    have hQc : ∀ i, IsCompact (Q i) := fun i =>
      (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_infEDist)
    have hQU : ∀ i, Q i ⊆ U := by
      intro i x hx
      by_contra hxU
      have h0 : (i : ℝ≥0∞)⁻¹ ≤ infEDist x Uᶜ := hx.2
      rw [infEDist_zero_of_mem (show x ∈ Uᶜ from hxU)] at h0
      exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top i) (le_antisymm h0 bot_le)
    have hUQ : ∀ x ∈ U, ∃ i, x ∈ Q i := by
      intro x hx
      have h0 : infEDist x Uᶜ ≠ 0 :=
        (infEDist_pos_iff_notMem_closure.2 (by rw [hU.isClosed_compl.closure_eq]; exact fun h => h hx)).ne'
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt h0
      obtain ⟨j, hj⟩ := exists_nat_ge ‖x‖
      refine ⟨max j k, ?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right]
        exact hj.trans (Nat.cast_le.2 (le_max_left j k))
      · exact (ENNReal.inv_le_inv.2 (Nat.cast_le.2 (le_max_right j k))).trans hk.le
    -- Lusin's theorem (Simon 1.17) for `f` and a finite Borel measure.
    have lusin : ∀ (ν : Measure (Amb n ℓ)), IsFiniteMeasure ν → ∀ A : Set (Amb n ℓ), MeasurableSet A →
        ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ C ⊆ A, IsClosed C ∧ ν (A \ C) < ε ∧ ContinuousOn f C := by
      intro ν hν A hA ε hε
      have : ν.WeaklyRegular := Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure ν
      obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε (ℚ × ℚ)
      -- For each rational interval, closed sets inside the parts of `A` where `f` is in / not in it.
      have hsplit : ∀ q : ℚ × ℚ, ∃ F ⊆ A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2, IsClosed F ∧
          ∃ F' ⊆ A \ f ⁻¹' Ioo (q.1 : ℝ) q.2, IsClosed F' ∧ ν (A \ (F ∪ F')) ≤ δ q := by
        intro q
        have hP : MeasurableSet (A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2) := hA.inter (hfm measurableSet_Ioo)
        have hN : MeasurableSet (A \ f ⁻¹' Ioo (q.1 : ℝ) q.2) := hA.diff (hfm measurableSet_Ioo)
        have hδ2 : (δ q : ℝ≥0∞) / 2 ≠ 0 :=
          (ENNReal.half_pos (ENNReal.coe_ne_zero.2 (hδpos q).ne')).ne'
        obtain ⟨F, hFP, hFc, hF⟩ := hP.exists_isClosed_sdiff_lt (measure_ne_top ν _) hδ2
        obtain ⟨F', hFN, hF'c, hF'⟩ := hN.exists_isClosed_sdiff_lt (measure_ne_top ν _) hδ2
        refine ⟨F, hFP, hFc, F', hFN, hF'c, ?_⟩
        calc ν (A \ (F ∪ F'))
            ≤ ν ((A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F ∪ (A \ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F') := by
              refine measure_mono fun x hx => ?_
              by_cases hfx : f x ∈ Ioo (q.1 : ℝ) q.2
              · exact Or.inl ⟨⟨hx.1, hfx⟩, fun h => hx.2 (Or.inl h)⟩
              · exact Or.inr ⟨⟨hx.1, hfx⟩, fun h => hx.2 (Or.inr h)⟩
          _ ≤ ν ((A ∩ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F) + ν ((A \ f ⁻¹' Ioo (q.1 : ℝ) q.2) \ F') :=
              measure_union_le _ _
          _ ≤ δ q / 2 + δ q / 2 := add_le_add hF.le hF'.le
          _ = δ q := ENNReal.add_halves _
      choose F hFP hFc F' hFN hF'c hFF' using hsplit
      refine ⟨⋂ q, (F q ∪ F' q), fun x hx => ?_, isClosed_iInter fun q => (hFc q).union (hF'c q),
        ?_, ?_⟩
      · rcases mem_iInter.1 hx (0, 0) with h | h
        · exact (hFP _ h).1
        · exact (hFN _ h).1
      · rw [sdiff_iInter]
        calc ν (⋃ q, A \ (F q ∪ F' q)) ≤ ∑' q, ν (A \ (F q ∪ F' q)) := measure_iUnion_le _
          _ ≤ ∑' q, (δ q : ℝ≥0∞) := ENNReal.tsum_le_tsum hFF'
          _ < ε := hδsum
      · rw [Metric.continuousOn_iff]
        intro x hx e he
        obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show f x - e < f x by linarith)
        obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show f x < f x + e by linarith)
        have hxF' : x ∉ F' (a, b) := fun h => (hFN _ h).2 ⟨ha₂, hb₁⟩
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hF'c (a, b)).isOpen_compl x hxF'
        refine ⟨r, hr, fun y hy hyx => ?_⟩
        have hyF : y ∈ F (a, b) := by
          rcases mem_iInter.1 hy (a, b) with h | h
          · exact h
          · exact absurd h (hball (mem_ball.2 hyx))
        obtain ⟨hy₁, hy₂⟩ := (hFP _ hyF).2
        rw [Real.dist_eq, abs_sub_lt_iff]
        constructor <;> linarith
    -- The Borel pieces `B i k` have finite `Hⁿ`-measure.
    set B : ℕ → ℕ → Set (Amb n ℓ) := fun i k => G ∩ Q i ∩ {x | 1 / ((k : ℝ) + 1) < f x}
    have hBm : ∀ i k, MeasurableSet (B i k) := fun i k =>
      (hGm.inter (hQc i).isClosed.measurableSet).inter (measurableSet_lt measurable_const hfm)
    have hBfin : ∀ i k, (μHE[n] : Measure (Amb n ℓ)) (B i k) < ⊤ := by
      intro i k
      have hc : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hint : ∫⁻ x in V.carrier ∩ Q i, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) < ⊤ :=
        Integrable.lintegral_lt_top (V.integrableOn_mult (Q i) (hQc i) (hQU i))
      have hle : ENNReal.ofReal (1 / ((k : ℝ) + 1)) * (μHE[n] : Measure (Amb n ℓ)) (B i k) ≤
          ∫⁻ x in V.carrier ∩ Q i, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) :=
        calc ENNReal.ofReal (1 / ((k : ℝ) + 1)) * (μHE[n] : Measure (Amb n ℓ)) (B i k)
            = ∫⁻ _ in B i k, ENNReal.ofReal (1 / ((k : ℝ) + 1)) ∂(μHE[n] : Measure (Amb n ℓ)) :=
              (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in B i k, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) :=
              setLIntegral_mono' (hBm i k) fun x hx =>
                ENNReal.ofReal_le_ofReal (by rw [hGf x hx.1.1]; exact hx.2.le)
          _ ≤ ∫⁻ x in V.carrier ∩ Q i, ENNReal.ofReal (V.mult x) ∂(μHE[n] : Measure (Amb n ℓ)) :=
              lintegral_mono_set fun x hx => ⟨hGM hx.1.1, hx.1.2⟩
      exact ENNReal.lt_top_of_mul_ne_top_right (hle.trans_lt hint).ne (ENNReal.ofReal_pos.2 hc).ne'
    -- Lusin pieces `C i k m ⊆ B i k`.
    have hC : ∀ i k m : ℕ, ∃ C ⊆ B i k, IsClosed C ∧
        (μHE[n] : Measure (Amb n ℓ)) (B i k \ C) < (m : ℝ≥0∞)⁻¹ ∧ ContinuousOn f C := by
      intro i k m
      obtain ⟨C, hCB, hCc, hCμ, hCf⟩ := lusin ((μHE[n] : Measure (Amb n ℓ)).restrict (B i k))
        (isFiniteMeasure_restrict.2 (hBfin i k).ne) (B i k) (hBm i k) (m : ℝ≥0∞)⁻¹
        (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))
      refine ⟨C, hCB, hCc, ?_, hCf⟩
      rwa [Measure.restrict_apply ((hBm i k).diff hCc.measurableSet),
        inter_eq_left.2 sdiff_subset] at hCμ
    choose C hCB hCc hCμ hCf using hC
    have hBnull : ∀ i k, (μHE[n] : Measure (Amb n ℓ)) (B i k \ ⋃ m, C i k m) = 0 := by
      intro i k
      by_contra h
      obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt h
      exact lt_asymm hm ((measure_mono (sdiff_subset_sdiff_right (subset_iUnion _ m))).trans_lt
        (hCμ i k m))
    -- Enumerate the pieces.
    refine ⟨fun j => C (Nat.unpair j).1 (Nat.unpair (Nat.unpair j).2).1
      (Nat.unpair (Nat.unpair j).2).2, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩
    · exact (hQc _).of_isClosed_subset (hCc _ _ _) ((hCB _ _ _).trans fun x hx => hx.1.2)
    · exact (hCB _ _ _).trans fun x hx => hGM hx.1.1
    · exact (hCf _ _ _).congr fun x hx => hGf x (hCB _ _ _ hx).1.1
    · exact (measure_mono (hCB _ _ _)).trans_lt (hBfin _ _)
    · refine measure_mono_null (fun x hx => ?_) (measure_union_null hMG
        (measure_iUnion_null fun i => measure_iUnion_null fun k => hBnull i k))
      by_cases hxG : x ∈ G
      · obtain ⟨i, hi⟩ := hUQ x (V.carrier_subset hx.1)
        have hfx : 0 < f x := by rw [← hGf x hxG]; exact V.mult_pos x hx.1
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hfx
        refine Or.inr (mem_iUnion₂.2 ⟨i, k, ⟨⟨hxG, hi⟩, hk⟩, fun hxC => ?_⟩)
        obtain ⟨m, hm⟩ := mem_iUnion.1 hxC
        refine hx.2 (mem_iUnion.2 ⟨Nat.pair i (Nat.pair k m), ?_⟩)
        simpa only [Nat.unpair_pair] using hm
      · exact Or.inl ⟨hx.1, hxG⟩
  have area_measure_eq : ∀ (F : Rn n → Amb n ℓ) {K : ℝ≥0} (hF : LipschitzWith K F) (A : Set (Rn n)) (hA : MeasurableSet A) (hinj : InjOn F A),
      (μHE[n] : Measure (Amb n ℓ)).restrict (F '' A) = ((volume.restrict A).withDensity (fun b => ((Poincare.SimonGMT.Chapter02.areaJacobianAt F b).toNNReal : ℝ≥0∞))).map F := by
    intro F K hF A hA hinj
    ext B hB
    have hFB : MeasurableSet (F ⁻¹' B) := hF.continuous.measurable hB
    rw [Measure.restrict_apply hB, Measure.map_apply hF.continuous.measurable hB,
      withDensity_apply _ hFB]
    have h := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hF hA hinj
      (B.indicator 1)
    rw [finrank_euclideanSpace_fin] at h
    rw [lintegral_indicator_one hB, Measure.restrict_apply hB] at h
    rw [h, ← lintegral_indicator hFB]
    refine lintegral_congr fun b => ?_
    by_cases hb : F b ∈ B
    · simp [hb, ENNReal.ofReal]
    · simp [hb]
  have linear_area_measure_eq : ∀ (L : Rn n →L[ℝ] Amb n ℓ),
      (μHE[n] : Measure (Amb n ℓ)).restrict (Set.range L) = (ENNReal.ofReal (L : Rn n →ₗ[ℝ] Amb n ℓ).normDet • (volume : Measure (Rn n))).map L := by
    intro L
    ext B hB
    have hLB : MeasurableSet (L ⁻¹' B) := L.continuous.measurable hB
    rw [Measure.restrict_apply hB, Measure.map_apply L.continuous.measurable hB,
      Measure.smul_apply, smul_eq_mul]
    have h := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
      (L : Rn n →ₗ[ℝ] Amb n ℓ) (L ⁻¹' B)
    rw [finrank_euclideanSpace_fin] at h
    rw [← h]
    congr 1
    ext y
    simp only [mem_inter_iff, mem_range, mem_image, mem_preimage, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨hy, c, rfl⟩
      exact ⟨c, hy, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨hc, c, rfl⟩
  have blowup_area_tendsto : ∀ (F : Rn n → Amb n ℓ) {K : ℝ≥0} (hF : LipschitzWith K F) (A : Set (Rn n)) (hA : MeasurableSet A) {lam : ℝ} (hlam : 0 < lam) (hbi : ∀ a ∈ A, ∀ b ∈ A, lam * ‖a - b‖ ≤ ‖F a - F b‖) (hgint : ∀ (c : Rn n) (t : ℝ), IntegrableOn (A.indicator (Poincare.SimonGMT.Chapter02.areaJacobianAt F)) (closedBall c t) volume) {a : Rn n} (ha : a ∈ A) (hdiff : DifferentiableAt ℝ F a) (hLinj : Function.Injective (fderiv ℝ F a)) (hleb : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ y in closedBall a (ρ * r), ‖A.indicator (Poincare.SimonGMT.Chapter02.areaJacobianAt F) y - A.indicator (Poincare.SimonGMT.Chapter02.areaJacobianAt F) a‖) (𝓝[>] 0) (𝓝 0)) (f : Amb n ℓ → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f),
      Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in F '' A, f (Poincare.SimonGMT.Chapter03.blowUpMap (F a) r z) ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 (∫ y in Set.range (fderiv ℝ F a), f y ∂(μHE[n] : Measure (Amb n ℓ)))) := by
    intro F K hF A hA lam hlam hbi hgint a ha hdiff hLinj hleb f hfc hfs
    set J := Poincare.SimonGMT.Chapter02.areaJacobianAt F with hJ
    set g : Rn n → ℝ := A.indicator J with hg
    set L := fderiv ℝ F a with hL
    have hη : ∀ (x : Amb n ℓ) (r : ℝ) (y : Amb n ℓ),
        Poincare.SimonGMT.Chapter03.blowUpMap x r y = r⁻¹ • (y - x) := fun _ _ _ => rfl
    have hinj : InjOn F A := fun b hb c hc h => by
      have h1 := hbi b hb c hc
      rw [h, sub_self, norm_zero] at h1
      have h2 : ‖b - c‖ ≤ 0 := by nlinarith [norm_nonneg (b - c)]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
    have hJm : Measurable J := Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt F
    have hJnn : ∀ b, 0 ≤ J b := Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg F
    set Ja : ℝ := J a with hJa
    have hJa_nn : 0 ≤ Ja := hJnn a
    have hga : g a = Ja := by rw [hg, Set.indicator_of_mem ha]
    -- Step 1: the blown-up area integral as an integral over the parameter space
    have hLHS : ∀ r : ℝ, ∫ z in F '' A, f (Poincare.SimonGMT.Chapter03.blowUpMap (F a) r z)
        ∂(μHE[n] : Measure (Amb n ℓ)) = ∫ b, g b * f (r⁻¹ • (F b - F a)) := by
      intro r
      rw [area_measure_eq F hF A hA hinj, integral_map hF.continuous.aemeasurable
        (by simp only [hη]; fun_prop : Continuous fun z =>
          f (Poincare.SimonGMT.Chapter03.blowUpMap (F a) r z)).aestronglyMeasurable,
        integral_withDensity_eq_integral_smul hJm.real_toNNReal, ← integral_indicator hA]
      congr 1
      ext b
      by_cases hb : b ∈ A
      · simp only [Set.indicator_of_mem hb, hg, hη, NNReal.smul_def, smul_eq_mul,
          Real.coe_toNNReal _ (hJnn b)]
      · simp [Set.indicator_of_notMem hb, hg]
    -- Step 2: the plane integral
    have hJL : (L : Rn n →ₗ[ℝ] Amb n ℓ).normDet = Ja := rfl
    have hRHS : ∫ y in Set.range L, f y ∂(μHE[n] : Measure (Amb n ℓ)) = Ja * ∫ c, f (L c) := by
      rw [linear_area_measure_eq L, integral_map L.continuous.aemeasurable
        hfc.aestronglyMeasurable, integral_smul_measure, hJL, ENNReal.toReal_ofReal hJa_nn,
        smul_eq_mul]
    have hscale : ∀ r : ℝ, 0 < r →
        ∫ c, f (L c) = (r ^ n)⁻¹ * ∫ b, f (r⁻¹ • L (b - a)) := by
      intro r hr
      have h1 : ∫ b, f (r⁻¹ • L (b - a)) = ∫ c, f (L (r⁻¹ • c)) := by
        have := integral_sub_right_eq_self (μ := (volume : Measure (Rn n)))
          (fun c => f (L (r⁻¹ • c))) a
        simpa only [map_smul] using this
      rw [h1, Measure.integral_comp_smul (volume : Measure (Rn n)) (fun c => f (L c)) r⁻¹,
        finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (pow_pos hr n), smul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ (pow_pos hr n).ne', one_mul]
    -- bounds for `f`
    obtain ⟨Cf, hCf⟩ := hfc.bounded_above_of_compact_support hfs
    have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
    obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := hfs.isCompact.isBounded.subset_closedBall 0
      refine ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy => ?_⟩
      apply image_eq_zero_of_notMem_tsupport
      intro hyt
      have h1 := hR₀ hyt
      rw [mem_closedBall, dist_zero_right] at h1
      linarith [le_max_left R₀ 1]
    -- a lower bound for the injective derivative
    obtain ⟨KL, hKLpos, hKL⟩ :=
      (LinearMap.injective_iff_antilipschitz (L : Rn n →ₗ[ℝ] Amb n ℓ)).1 hLinj
    set lamL : ℝ := ((KL : ℝ))⁻¹ with hlamL_def
    have hKL0 : (0 : ℝ) < KL := by exact_mod_cast hKLpos
    have hlamL : 0 < lamL := inv_pos.2 hKL0
    have hLlow : ∀ v, lamL * ‖v‖ ≤ ‖L v‖ := by
      intro v
      have h1 := hKL.le_mul_dist v 0
      simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at h1
      rw [hlamL_def, inv_mul_le_iff₀ hKL0]
      exact h1
    set ρ : ℝ := (R + 1) / lam + (R + 1) / lamL with hρ_def
    have hρ : 0 < ρ := by positivity
    -- outside `B_{ρ r}(a)` both integrands vanish
    have hsupp1 : ∀ r : ℝ, 0 < r → ∀ b, b ∉ closedBall a (ρ * r) →
        g b * f (r⁻¹ • (F b - F a)) = 0 := by
      intro r hr b hb
      by_cases hbA : b ∈ A
      · rw [hR _ ?_, mul_zero]
        rw [mem_closedBall, dist_eq_norm, not_le] at hb
        have h1 := hbi b hbA a ha
        rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le, ← div_eq_inv_mul, lt_div_iff₀ hr]
        have h2 : (R + 1) / lam * r ≤ ρ * r :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hr.le
        have h3 : lam * ((R + 1) / lam * r) = (R + 1) * r := by field_simp
        nlinarith
      · rw [hg, Set.indicator_of_notMem hbA, zero_mul]
    have hsupp2 : ∀ r : ℝ, 0 < r → ∀ b, b ∉ closedBall a (ρ * r) →
        f (r⁻¹ • L (b - a)) = 0 := by
      intro r hr b hb
      apply hR
      rw [mem_closedBall, dist_eq_norm, not_le] at hb
      have h1 := hLlow (b - a)
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le, ← div_eq_inv_mul, lt_div_iff₀ hr]
      have h2 : (R + 1) / lamL * r ≤ ρ * r :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hr.le
      have h3 : lamL * ((R + 1) / lamL * r) = (R + 1) * r := by field_simp
      nlinarith
    -- integrability of both integrands
    have hint1 : ∀ r : ℝ, 0 < r → Integrable (fun b => g b * f (r⁻¹ • (F b - F a))) := by
      intro r hr
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ (hsupp1 r hr)
      refine (hgint a (ρ * r)).mul_bdd (c := Cf) ?_ (Eventually.of_forall fun b => hCf _)
      exact (hfc.comp ((hF.continuous.sub continuous_const).const_smul r⁻¹)).aestronglyMeasurable
    have hint2 : ∀ r : ℝ, 0 < r → Integrable (fun b => Ja * f (r⁻¹ • L (b - a))) := by
      intro r hr
      refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
      exact HasCompactSupport.intro (isCompact_closedBall a (ρ * r))
        fun b hb => by rw [hsupp2 r hr b hb, mul_zero]
    -- the difference as one integral
    have hdiffint : ∀ r : ℝ, 0 < r →
        (r ^ n)⁻¹ * ∫ z in F '' A, f (Poincare.SimonGMT.Chapter03.blowUpMap (F a) r z)
          ∂(μHE[n] : Measure (Amb n ℓ)) - ∫ y in Set.range L, f y ∂(μHE[n] : Measure (Amb n ℓ)) =
        (r ^ n)⁻¹ * ∫ b, (g b * f (r⁻¹ • (F b - F a)) - Ja * f (r⁻¹ • L (b - a))) := by
      intro r hr
      rw [hLHS, hRHS, hscale r hr, integral_sub (hint1 r hr) (hint2 r hr), integral_const_mul]
      ring
    -- volume of the balls
    set c₁ : ℝ := (volume (closedBall (0 : Rn n) 1)).toReal with hc₁
    have hvol : ∀ t : ℝ, 0 ≤ t → (volume (closedBall a t)).toReal = t ^ n * c₁ := by
      intro t ht
      rw [Measure.addHaar_closedBall' volume a ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (pow_nonneg ht _), finrank_euclideanSpace_fin]
    have hc₁0 : 0 ≤ c₁ := ENNReal.toReal_nonneg
    -- the estimate
    have hmain : Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ b,
        (g b * f (r⁻¹ • (F b - F a)) - Ja * f (r⁻¹ • L (b - a)))) (𝓝[>] 0) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      set ε₁ : ℝ := ε / (2 * (Ja * ρ ^ n * c₁ + 1)) with hε₁
      have hε₁0 : 0 < ε₁ := by positivity
      obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.1
        (hfs.uniformContinuous_of_continuous hfc) ε₁ hε₁0
      have hlo := (hdiff.hasFDerivAt.isLittleO).def (show (0 : ℝ) < δ / (2 * ρ) by positivity)
      obtain ⟨η, hη0, hηb⟩ := Metric.eventually_nhds_iff.1 hlo
      have hleb' := (Metric.tendsto_nhds.1 (hleb ρ hρ)) (ε / (2 * (Cf + 1))) (by positivity)
      filter_upwards [hleb', Ioo_mem_nhdsGT (show (0 : ℝ) < η / ρ by positivity)] with r hr1 hr2
      have hr : 0 < r := hr2.1
      have hρr : ρ * r < η := by
        have := hr2.2
        rw [lt_div_iff₀ hρ] at this
        linarith
      rw [Real.dist_eq, sub_zero] at hr1 ⊢
      -- pointwise bound
      have hpt : ∀ b, ‖g b * f (r⁻¹ • (F b - F a)) - Ja * f (r⁻¹ • L (b - a))‖ ≤
          (closedBall a (ρ * r)).indicator (fun b => Cf * ‖g b - g a‖ + Ja * ε₁) b := by
        intro b
        by_cases hb : b ∈ closedBall a (ρ * r)
        · rw [Set.indicator_of_mem hb]
          have hba : ‖b - a‖ ≤ ρ * r := by rwa [mem_closedBall, dist_eq_norm] at hb
          have hdist : dist (r⁻¹ • (F b - F a)) (r⁻¹ • L (b - a)) < δ := by
            rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le]
            have h1 : ‖F b - F a - L (b - a)‖ ≤ δ / (2 * ρ) * ‖b - a‖ :=
              hηb (by rw [dist_eq_norm]; linarith)
            have h2 : δ / (2 * ρ) * ‖b - a‖ ≤ δ / (2 * ρ) * (ρ * r) :=
              mul_le_mul_of_nonneg_left hba (by positivity)
            have h3 : δ / (2 * ρ) * (ρ * r) = δ / 2 * r := by field_simp
            rw [← div_eq_inv_mul, div_lt_iff₀ hr]
            nlinarith
          have hfd := hδ hdist
          rw [Real.dist_eq] at hfd
          calc ‖g b * f (r⁻¹ • (F b - F a)) - Ja * f (r⁻¹ • L (b - a))‖
              = ‖(g b - g a) * f (r⁻¹ • (F b - F a)) +
                  Ja * (f (r⁻¹ • (F b - F a)) - f (r⁻¹ • L (b - a)))‖ := by
                rw [hga]; ring_nf
            _ ≤ ‖g b - g a‖ * Cf + Ja * ε₁ := by
                refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
                · rw [norm_mul]
                  exact mul_le_mul_of_nonneg_left (hCf _) (norm_nonneg _)
                · rw [norm_mul, Real.norm_of_nonneg hJa_nn, Real.norm_eq_abs]
                  exact mul_le_mul_of_nonneg_left hfd.le hJa_nn
            _ = Cf * ‖g b - g a‖ + Ja * ε₁ := by ring
        · rw [Set.indicator_of_notMem hb, hsupp1 r hr b hb, hsupp2 r hr b hb, mul_zero,
            sub_zero, norm_zero]
      have hb1 : IntegrableOn (fun b => Cf * ‖g b - g a‖) (closedBall a (ρ * r)) :=
        ((hgint a (ρ * r)).sub (integrableOn_const (measure_closedBall_lt_top).ne)).norm.const_mul Cf
      have hb2 : IntegrableOn (fun _ : Rn n => Ja * ε₁) (closedBall a (ρ * r)) :=
        integrableOn_const (measure_closedBall_lt_top).ne
      have hb3 : IntegrableOn (fun b => Cf * ‖g b - g a‖ + Ja * ε₁) (closedBall a (ρ * r)) :=
        hb1.add hb2
      have hI := norm_integral_le_of_norm_le
        ((integrable_indicator_iff measurableSet_closedBall).2 hb3)
        (Eventually.of_forall hpt)
      have hsplit : ∫ b in closedBall a (ρ * r), (Cf * ‖g b - g a‖ + Ja * ε₁) =
          Cf * (∫ b in closedBall a (ρ * r), ‖g b - g a‖) + (ρ * r) ^ n * c₁ * (Ja * ε₁) := by
        rw [integral_add hb1 hb2, integral_const_mul, setIntegral_const, smul_eq_mul,
          measureReal_def, hvol (ρ * r) (by positivity)]
      rw [integral_indicator measurableSet_closedBall] at hI
      beta_reduce at hI
      rw [hsplit] at hI
      have hrn : 0 < r ^ n := pow_pos hr n
      rw [abs_mul, abs_of_pos (inv_pos.2 hrn)]
      calc (r ^ n)⁻¹ * |∫ b, (g b * f (r⁻¹ • (F b - F a)) - Ja * f (r⁻¹ • L (b - a)))|
          ≤ (r ^ n)⁻¹ * (Cf * (∫ b in closedBall a (ρ * r), ‖g b - g a‖) +
              (ρ * r) ^ n * c₁ * (Ja * ε₁)) :=
            mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact hI) (inv_pos.2 hrn).le
        _ = Cf * ((r ^ n)⁻¹ * ∫ b in closedBall a (ρ * r), ‖g b - g a‖) +
              Ja * ρ ^ n * c₁ * ε₁ := by
            rw [mul_pow]; field_simp
        _ < ε / 2 + ε / 2 := by
            refine add_lt_add_of_le_of_lt ?_ ?_
            · have hX : (r ^ n)⁻¹ * ∫ b in closedBall a (ρ * r), ‖g b - g a‖ ≤
                  ε / (2 * (Cf + 1)) := (le_abs_self _).trans hr1.le
              calc Cf * ((r ^ n)⁻¹ * ∫ b in closedBall a (ρ * r), ‖g b - g a‖)
                  ≤ Cf * (ε / (2 * (Cf + 1))) := mul_le_mul_of_nonneg_left hX hCf0
                _ ≤ ε / 2 := by
                  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
                  nlinarith
            · rw [hε₁, mul_div_assoc']
              rw [div_lt_div_iff₀ (by positivity) (by positivity)]
              nlinarith [mul_nonneg (mul_nonneg hJa_nn (pow_nonneg hρ.le n)) hc₁0]
        _ = ε := add_halves ε
    have hfin := hmain.congr' (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hdiffint r hr).symm)
    simpa using hfin.add_const (∫ y in Set.range L, f y ∂(μHE[n] : Measure (Amb n ℓ)))
  have jac_integrableOn : ∀ (F : Rn n → Amb n ℓ) {K : ℝ≥0} (hF : LipschitzWith K F) (A : Set (Rn n)) (hA : MeasurableSet A) (hinj : InjOn F A) (c : Rn n) (t : ℝ),
      IntegrableOn (A.indicator (Poincare.SimonGMT.Chapter02.areaJacobianAt F)) (closedBall c t) volume := by
    intro F K hF A hA hinj c t
    have hJm := Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt F
    have hJnn := Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg F
    rw [IntegrableOn, integrable_indicator_iff hA, IntegrableOn,
      Measure.restrict_restrict hA]
    refine ⟨hJm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hJnn)]
    have h := Poincare.SimonGMT.Chapter02.injective_area_formula_lipschitz hF
      (hA.inter (measurableSet_closedBall (x := c) (ε := t))) (hinj.mono inter_subset_left)
    rw [finrank_euclideanSpace_fin] at h
    rw [← h]
    calc (μHE[n] : Measure (Amb n ℓ)) (F '' (A ∩ closedBall c t))
        ≤ (K : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) (A ∩ closedBall c t) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            hF.lipschitzOnWith
      _ < ⊤ := by
          have hH : (μHE[n] : Measure (Rn n)) = volume := by
            have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Rn n)
            rwa [finrank_euclideanSpace_fin] at this
          rw [hH]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
            ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top)
  have leb_points : ∀ (g : Rn n → ℝ) (hg : ∀ (c : Rn n) (t : ℝ), IntegrableOn g (closedBall c t) volume),
      ∀ᵐ a ∂(volume : Measure (Rn n)), ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ y in closedBall a (ρ * r), ‖g y - g a‖) (𝓝[>] 0) (𝓝 0) := by
    intro g hg
    have hloc : LocallyIntegrable g volume := fun x =>
      ⟨closedBall x 1, closedBall_mem_nhds x one_pos, hg x 1⟩
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc 1] with a ha ρ hρ
    have hρt : Tendsto (fun r : ℝ => ρ * r) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa only [mul_zero, id_eq] using
          ((tendsto_id.mono_left inf_le_left : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).const_mul ρ)
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos hρ hr
    have h1 := ha (fun _ => a) (fun r => ρ * r) hρt (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact mem_closedBall_self (by rw [one_mul]; exact (mul_pos hρ hr).le))
    set c₁ : ℝ := (volume (closedBall (0 : Rn n) 1)).toReal with hc₁
    have hvol : ∀ t : ℝ, 0 ≤ t → (volume (closedBall a t)).toReal = t ^ n * c₁ := by
      intro t ht
      rw [Measure.addHaar_closedBall' volume a ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (pow_nonneg ht _), finrank_euclideanSpace_fin]
    have hc₁0 : 0 < c₁ := ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne'
      measure_closedBall_lt_top.ne
    have h2 := h1.const_mul (ρ ^ n * c₁)
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [setAverage_eq, measureReal_def, hvol _ (mul_pos hρ hr).le, smul_eq_mul, mul_pow]
    field_simp
  have weighted_tangent_at : ∀ (Kset : Set (Amb n ℓ)) (hKc : IsCompact Kset) (hKM : Kset ⊆ V.carrier) (hKcont : ContinuousOn V.mult Kset) (hKfin : (μHE[n] : Measure (Amb n ℓ)) Kset < ⊤) (S : Set (Amb n ℓ)) (hSm : MeasurableSet S) (x : Amb n ℓ) (hxK : x ∈ Kset) (P : Submodule ℝ (Amb n ℓ)) (hP : Module.finrank ℝ P = n) (hblow : ∀ f : Amb n ℓ → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 (∫ y in (P : Set (Amb n ℓ)), f y ∂(μHE[n] : Measure (Amb n ℓ))))) (C : ℝ) (hC : 0 ≤ C) (hSball : ∀ r : ℝ, 0 < r → (μHE[n] : Measure (Amb n ℓ)) (S ∩ closedBall x r) ≤ ENNReal.ofReal (C * r ^ n)) (hG3 : Tendsto (fun r : ℝ => V.weight (closedBall x r \ Kset) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0)) (hG4 : Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) ((Kset \ S) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0)) (hG5 : Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) ((S \ Kset) ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0)),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P := by
    intro Kset hKc hKM hKcont hKfin S hSm x hxK P hP hblow C hC hSball hG3 hG4 hG5
    have hrsod := Submission.rsod_blowUp_setIntegral_eq
    set H : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)) with hH
    set μ : Measure (Amb n ℓ) := V.weight with hμ
    have hη : ∀ (x : Amb n ℓ) (r : ℝ) (y : Amb n ℓ),
        Poincare.SimonGMT.Chapter03.blowUpMap x r y = r⁻¹ • (y - x) := fun _ _ _ => rfl
    have hKm : MeasurableSet Kset := hKc.isClosed.measurableSet
    -- `∫ g dμ_V = ∫_M g θ dHⁿ`
    have hweight : ∀ g : Amb n ℓ → ℝ, ∫ z, g z ∂μ = ∫ z in V.carrier, g z * V.mult z ∂H := by
      intro g
      rw [hμ, RectifiableVarifold.weight, integral_withDensity_eq_integral_toReal_smul₀
        V.aemeasurable_mult.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem₀ V.nullMeasurableSet_carrier] with z hz
      rw [ENNReal.toReal_ofReal (V.mult_pos z hz).le, smul_eq_mul, mul_comm]
    -- conversion of an `r⁻ⁿ`-density statement to real numbers at scale `R r`
    have hconv : ∀ φ : ℝ → ℝ≥0∞, Tendsto (fun r : ℝ => φ r / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) →
        ∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * (φ (R * r)).toReal) (𝓝[>] 0) (𝓝 0) := by
      intro φ hφ R hR
      have hRt : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · simpa only [mul_zero, id_eq] using
            ((tendsto_id.mono_left inf_le_left : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).const_mul R)
        · filter_upwards [self_mem_nhdsWithin] with r hr
          exact mul_pos hR hr
      have h1 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hφ.comp hRt)).const_mul (R ^ n)
      rw [ENNReal.toReal_zero, mul_zero] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (0 : ℝ) < r := hr
      simp only [Function.comp_apply, ENNReal.toReal_div]
      rw [ENNReal.toReal_ofReal (pow_nonneg (mul_pos hR hr').le n), mul_pow]
      field_simp
    refine ⟨hP, fun f => ?_⟩
    -- data about the test function
    obtain ⟨Cf, hCf⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
    obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      refine ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy => ?_⟩
      apply image_eq_zero_of_notMem_tsupport
      intro hyt
      have h1 := hR₀ hyt
      rw [mem_closedBall, dist_zero_right] at h1
      linarith [le_max_left R₀ 1]
    set g : ℝ → Amb n ℓ → ℝ := fun r z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) with hg
    have hg0 : ∀ r : ℝ, 0 < r → ∀ z, z ∉ closedBall x (R * r) → g r z = 0 := by
      intro r hr z hz
      apply hR
      rw [mem_closedBall, dist_eq_norm, not_le] at hz
      rw [hη, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le, ← div_eq_inv_mul, lt_div_iff₀ hr]
      linarith
    have hgc : ∀ r : ℝ, Continuous (g r) := fun r => by
      simp only [hg, hη]
      exact f.continuous.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)
    have hgb : ∀ r z, ‖g r z‖ ≤ Cf := fun r z => hCf _
    -- `‖∫_T g_r dν‖ ≤ C_f ν(B_{Rr}(x) ∩ T)`
    have hsetbound : ∀ (ν : Measure (Amb n ℓ)) (T : Set (Amb n ℓ)) (r : ℝ), 0 < r →
        ν (closedBall x (R * r) ∩ T) < ⊤ →
        ‖∫ z in T, g r z ∂ν‖ ≤ Cf * (ν (closedBall x (R * r) ∩ T)).toReal := by
      intro ν T r hr hfin
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν.restrict T) (hg0 r hr),
        Measure.restrict_restrict measurableSet_closedBall]
      have : IsFiniteMeasure (ν.restrict (closedBall x (R * r) ∩ T)) :=
        isFiniteMeasure_restrict.2 hfin.ne
      refine (MeasureTheory.norm_integral_le_of_norm_le_const
        (Eventually.of_forall fun z => hgb r z)).trans_eq ?_
      rw [measureReal_def, Measure.restrict_apply_univ]
    -- a compact neighbourhood of `K` inside `U`
    obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hKc.exists_cthickening_subset_open hU (hKM.trans V.carrier_subset)
    have hLc : IsCompact (cthickening δ₀ Kset) := hKc.cthickening
    have hμL : μ (cthickening δ₀ Kset) < ⊤ := by
      calc μ (cthickening δ₀ Kset)
          = ∫⁻ z in cthickening δ₀ Kset, ENNReal.ofReal (V.mult z) ∂(H.restrict V.carrier) := by
            rw [hμ, RectifiableVarifold.weight, withDensity_apply _ isClosed_cthickening.measurableSet]
        _ = ∫⁻ z in V.carrier ∩ cthickening δ₀ Kset, ENNReal.ofReal (V.mult z) ∂H := by
            rw [Measure.restrict_restrict isClosed_cthickening.measurableSet, inter_comm]
        _ < ⊤ := (V.integrableOn_mult _ hLc hδ₀U).lintegral_lt_top
    have hBL : ∀ r : ℝ, R * r < δ₀ → closedBall x (R * r) ⊆ cthickening δ₀ Kset :=
      fun r h => (closedBall_subset_closedBall h.le).trans (closedBall_subset_cthickening hxK δ₀)
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ R * r < δ₀ := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ₀ / R by positivity)] with r hr
      exact ⟨hr.1, by have := hr.2; rw [lt_div_iff₀ hR0] at this; linarith⟩
    -- `μ_V` on `K` is `θ Hⁿ`
    have hKweight : ∀ φ : Amb n ℓ → ℝ, ∫ z in Kset, φ z ∂μ = ∫ z in Kset, φ z * V.mult z ∂H := by
      intro φ
      have hres : μ.restrict Kset = (H.restrict Kset).withDensity (fun z => ENNReal.ofReal (V.mult z)) := by
        rw [hμ, RectifiableVarifold.weight, restrict_withDensity hKm, Measure.restrict_restrict hKm,
          inter_eq_left.2 hKM]
      rw [hres, integral_withDensity_eq_integral_toReal_smul₀
        ((V.aemeasurable_mult.mono_measure (Measure.restrict_mono hKM le_rfl)).ennreal_ofReal)
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hKm] with z hz
      rw [ENNReal.toReal_ofReal (V.mult_pos z (hKM hz)).le, smul_eq_mul, mul_comm]
    have hθK : IntegrableOn V.mult Kset H := by
      have := V.integrableOn_mult Kset hKc (hKM.trans V.carrier_subset)
      rwa [inter_eq_right.2 hKM] at this
    have hgK : ∀ r, IntegrableOn (g r) Kset H := fun r =>
      Measure.integrableOn_of_bounded hKfin.ne (hgc r).aestronglyMeasurable
        (Eventually.of_forall fun z => hgb r z)
    have hgθK : ∀ r, IntegrableOn (fun z => g r z * V.mult z) Kset H := fun r =>
      hθK.bdd_mul (hgc r).aestronglyMeasurable (Eventually.of_forall fun z => hgb r z)
    have hθx : 0 ≤ V.mult x := (V.mult_pos x (hKM hxK)).le
    have hμB : ∀ r : ℝ, R * r < δ₀ → μ (closedBall x (R * r)) < ⊤ := fun r h =>
      (measure_mono (hBL r h)).trans_lt hμL
    have hSB : ∀ r : ℝ, 0 < r → H (closedBall x (R * r) ∩ S) < ⊤ := fun r hr => by
      rw [inter_comm]
      exact (hSball (R * r) (mul_pos hR0 hr)).trans_lt ENNReal.ofReal_lt_top
    -- integrability of `g_r` for `μ` and on `S`
    have hgμ : ∀ r : ℝ, 0 < r → R * r < δ₀ → Integrable (g r) μ := fun r hr h =>
      (Measure.integrableOn_of_bounded (hμB r h).ne (hgc r).aestronglyMeasurable
        (Eventually.of_forall fun z => hgb r z)).integrable_of_forall_notMem_eq_zero (hg0 r hr)
    have hgS : ∀ r : ℝ, 0 < r → IntegrableOn (g r) S H := fun r hr => by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall x (R * r)) ?_ (hg0 r hr)
      refine Measure.integrableOn_of_bounded ?_ (hgc r).aestronglyMeasurable
        (Eventually.of_forall fun z => hgb r z)
      rw [Measure.restrict_apply measurableSet_closedBall]
      exact (hSB r hr).ne
    -- the decomposition
    set E1 : ℝ → ℝ := fun r => (r ^ n)⁻¹ * ∫ z in Ksetᶜ, g r z ∂μ with hE1def
    set E2 : ℝ → ℝ := fun r => (r ^ n)⁻¹ * (∫ z in Kset, g r z * V.mult z ∂H -
      V.mult x * ∫ z in Kset, g r z ∂H) with hE2def
    set E3 : ℝ → ℝ := fun r => (r ^ n)⁻¹ * (∫ z in Kset, g r z ∂H - ∫ z in S, g r z ∂H) with hE3def
    set E4 : ℝ → ℝ := fun r => (r ^ n)⁻¹ * ∫ z in S, g r z ∂H with hE4def
    have hident : ∀ᶠ r in 𝓝[>] (0 : ℝ), E1 r + E2 r + V.mult x * E3 r + V.mult x * E4 r =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier, f y * V.mult (x + r • y) ∂H := by
      filter_upwards [hev] with r hr
      rw [hrsod n ℓ V.carrier f V.mult x r hr.1]
      have h1 : ∫ z in V.carrier, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z ∂H =
          ∫ z in Kset, g r z ∂μ + ∫ z in Ksetᶜ, g r z ∂μ := by
        rw [integral_add_compl hKm (hgμ r hr.1 hr.2), hweight]
      rw [h1, hKweight]
      simp only [hE1def, hE2def, hE3def, hE4def]
      ring
    -- the limits of the four pieces
    have hE1 : Tendsto E1 (𝓝[>] 0) (𝓝 0) := by
      have hlim := (hconv (fun r => μ (closedBall x r \ Kset)) hG3 R hR0).const_mul Cf
      rw [mul_zero] at hlim
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [hev] with r hr
      rw [hE1def]
      beta_reduce
      rw [norm_mul, Real.norm_of_nonneg (inv_pos.2 (pow_pos hr.1 n)).le]
      have hb := hsetbound μ Ksetᶜ r hr.1 ((measure_mono inter_subset_left).trans_lt (hμB r hr.2))
      rw [← sdiff_eq] at hb
      calc (r ^ n)⁻¹ * ‖∫ z in Ksetᶜ, g r z ∂μ‖
          ≤ (r ^ n)⁻¹ * (Cf * (μ (closedBall x (R * r) \ Kset)).toReal) :=
            mul_le_mul_of_nonneg_left hb (inv_pos.2 (pow_pos hr.1 n)).le
        _ = Cf * ((r ^ n)⁻¹ * (μ (closedBall x (R * r) \ Kset)).toReal) := by ring
    have hG4' := hconv (fun r => H ((Kset \ S) ∩ closedBall x r)) hG4 R hR0
    have hG5' := hconv (fun r => H ((S \ Kset) ∩ closedBall x r)) hG5 R hR0
    have hE3 : Tendsto E3 (𝓝[>] 0) (𝓝 0) := by
      have hlim := (hG4'.add hG5').const_mul Cf
      rw [add_zero, mul_zero] at hlim
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [hev] with r hr
      have hsplit : ∫ z in Kset, g r z ∂H - ∫ z in S, g r z ∂H =
          ∫ z in Kset \ S, g r z ∂H - ∫ z in S \ Kset, g r z ∂H := by
        rw [← integral_inter_add_sdiff hSm (hgK r), ← integral_inter_add_sdiff hKm (hgS r hr.1),
          inter_comm S Kset]
        ring
      have hb1 := hsetbound H (Kset \ S) r hr.1
        ((measure_mono (inter_subset_right.trans sdiff_subset)).trans_lt hKfin)
      have hb2 := hsetbound H (S \ Kset) r hr.1
        ((measure_mono (inter_subset_inter_right _ sdiff_subset)).trans_lt (hSB r hr.1))
      rw [inter_comm] at hb1 hb2
      rw [hE3def]
      beta_reduce
      rw [hsplit, norm_mul, Real.norm_of_nonneg (inv_pos.2 (pow_pos hr.1 n)).le]
      calc (r ^ n)⁻¹ * ‖∫ z in Kset \ S, g r z ∂H - ∫ z in S \ Kset, g r z ∂H‖
          ≤ (r ^ n)⁻¹ * (Cf * (H ((Kset \ S) ∩ closedBall x (R * r))).toReal +
              Cf * (H ((S \ Kset) ∩ closedBall x (R * r))).toReal) :=
            mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hb1 hb2))
              (inv_pos.2 (pow_pos hr.1 n)).le
        _ = Cf * ((r ^ n)⁻¹ * (H ((Kset \ S) ∩ closedBall x (R * r))).toReal +
              (r ^ n)⁻¹ * (H ((S \ Kset) ∩ closedBall x (R * r))).toReal) := by ring
    have hE2 : Tendsto E2 (𝓝[>] 0) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      set M₀ : ℝ := 1 + C * R ^ n with hM₀
      have hM₀pos : 0 < M₀ := by
        have := mul_nonneg hC (pow_nonneg hR0.le n); rw [hM₀]; linarith
      set ε' : ℝ := ε / (2 * (Cf + 1) * M₀) with hε'
      have hε'0 : 0 < ε' := by positivity
      obtain ⟨δθ, hδθ, hθδ⟩ := Metric.continuousWithinAt_iff.1 (hKcont x hxK) ε' hε'0
      have hG4ev := (Metric.tendsto_nhds.1 hG4') 1 one_pos
      filter_upwards [hev, hG4ev, Ioo_mem_nhdsGT (show (0 : ℝ) < δθ / R by positivity)]
        with r hr hr4 hr5
      have hrn : 0 < r ^ n := pow_pos hr.1 n
      have hRr : R * r < δθ := by have := hr5.2; rw [lt_div_iff₀ hR0] at this; linarith
      rw [Real.dist_eq, sub_zero] at hr4 ⊢
      -- pointwise bound on `K`
      have hpt : ∀ᵐ z ∂H.restrict Kset, ‖g r z * V.mult z - V.mult x * g r z‖ ≤
          (closedBall x (R * r)).indicator (fun _ => Cf * ε') z := by
        filter_upwards [ae_restrict_mem hKm] with z hz
        by_cases hzB : z ∈ closedBall x (R * r)
        · rw [Set.indicator_of_mem hzB]
          have hd : dist (V.mult z) (V.mult x) < ε' := hθδ hz (lt_of_le_of_lt hzB hRr)
          rw [Real.dist_eq] at hd
          calc ‖g r z * V.mult z - V.mult x * g r z‖ = ‖g r z‖ * |V.mult z - V.mult x| := by
                rw [show g r z * V.mult z - V.mult x * g r z = g r z * (V.mult z - V.mult x) by ring,
                  norm_mul, Real.norm_eq_abs (V.mult z - V.mult x)]
            _ ≤ Cf * ε' := mul_le_mul (hgb r z) hd.le (abs_nonneg _) hCf0
        · rw [Set.indicator_of_notMem hzB, hg0 r hr.1 z hzB]
          simp
      have hKBfin : H (closedBall x (R * r) ∩ Kset) < ⊤ :=
        (measure_mono inter_subset_right).trans_lt hKfin
      have hint_ind : Integrable ((closedBall x (R * r)).indicator (fun _ => Cf * ε')) (H.restrict Kset) := by
        rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall]
        exact hKBfin.ne
      have hI := norm_integral_le_of_norm_le hint_ind hpt
      rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
        measureReal_def, Measure.restrict_apply measurableSet_closedBall] at hI
      have hdiffK : ∫ z in Kset, g r z * V.mult z ∂H - V.mult x * ∫ z in Kset, g r z ∂H =
          ∫ z in Kset, (g r z * V.mult z - V.mult x * g r z) ∂H := by
        rw [integral_sub (hgθK r) ((hgK r).const_mul _), integral_const_mul]
      -- mass of `K` in the ball
      have hKB : (H (closedBall x (R * r) ∩ Kset)).toReal ≤
          (H ((Kset \ S) ∩ closedBall x (R * r))).toReal + C * (R * r) ^ n := by
        have h1 : H (closedBall x (R * r) ∩ Kset) ≤
            H ((Kset \ S) ∩ closedBall x (R * r)) + H (S ∩ closedBall x (R * r)) := by
          refine (measure_mono ?_).trans (measure_union_le _ _)
          intro z hz
          by_cases hzS : z ∈ S
          · exact Or.inr ⟨hzS, hz.1⟩
          · exact Or.inl ⟨⟨hz.2, hzS⟩, hz.1⟩
        have h2 := hSball (R * r) (mul_pos hR0 hr.1)
        have hfin1 : H ((Kset \ S) ∩ closedBall x (R * r)) ≠ ⊤ :=
          ((measure_mono (inter_subset_left.trans sdiff_subset)).trans_lt hKfin).ne
        calc (H (closedBall x (R * r) ∩ Kset)).toReal
            ≤ (H ((Kset \ S) ∩ closedBall x (R * r)) + H (S ∩ closedBall x (R * r))).toReal :=
              ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1,
                (h2.trans_lt ENNReal.ofReal_lt_top).ne⟩) h1
          _ = (H ((Kset \ S) ∩ closedBall x (R * r))).toReal + (H (S ∩ closedBall x (R * r))).toReal :=
              ENNReal.toReal_add hfin1 (h2.trans_lt ENNReal.ofReal_lt_top).ne
          _ ≤ (H ((Kset \ S) ∩ closedBall x (R * r))).toReal + C * (R * r) ^ n := by
              gcongr
              exact ENNReal.toReal_le_of_le_ofReal
                (mul_nonneg hC (pow_nonneg (mul_pos hR0 hr.1).le n)) h2
      have hX : (r ^ n)⁻¹ * (H ((Kset \ S) ∩ closedBall x (R * r))).toReal < 1 :=
        (le_abs_self _).trans_lt hr4
      rw [hE2def]
      beta_reduce
      rw [hdiffK, abs_mul, abs_of_pos (inv_pos.2 hrn)]
      calc (r ^ n)⁻¹ * |∫ z in Kset, (g r z * V.mult z - V.mult x * g r z) ∂H|
          ≤ (r ^ n)⁻¹ * ((H (closedBall x (R * r) ∩ Kset)).toReal * (Cf * ε')) :=
            mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact hI) (inv_pos.2 hrn).le
        _ = Cf * ε' * ((r ^ n)⁻¹ * (H (closedBall x (R * r) ∩ Kset)).toReal) := by ring
        _ ≤ Cf * ε' * ((r ^ n)⁻¹ * (H ((Kset \ S) ∩ closedBall x (R * r))).toReal + C * R ^ n) := by
            gcongr
            calc (r ^ n)⁻¹ * (H (closedBall x (R * r) ∩ Kset)).toReal
                ≤ (r ^ n)⁻¹ * ((H ((Kset \ S) ∩ closedBall x (R * r))).toReal + C * (R * r) ^ n) :=
                  mul_le_mul_of_nonneg_left hKB (inv_pos.2 hrn).le
              _ = (r ^ n)⁻¹ * (H ((Kset \ S) ∩ closedBall x (R * r))).toReal + C * R ^ n := by
                  rw [mul_pow]; field_simp
        _ ≤ Cf * ε' * M₀ := by
            gcongr
            rw [hM₀]; linarith
        _ < ε := by
            rw [hε']
            rw [show Cf * (ε / (2 * (Cf + 1) * M₀)) * M₀ = ε * (Cf / (2 * (Cf + 1))) by
              field_simp]
            have : Cf / (2 * (Cf + 1)) < 1 := by
              rw [div_lt_one (by positivity)]; linarith
            nlinarith
    have hE4 : Tendsto E4 (𝓝[>] 0) (𝓝 (∫ y in (P : Set (Amb n ℓ)), f y ∂H)) :=
      hblow f f.continuous f.hasCompactSupport
    have hlim := ((hE1.add hE2).add (hE3.const_mul (V.mult x))).add (hE4.const_mul (V.mult x))
    have h0 : (0 : ℝ) + 0 + V.mult x * 0 + V.mult x * ∫ y in (P : Set (Amb n ℓ)), f y ∂H =
        V.mult x * ∫ y in (P : Set (Amb n ℓ)), f y ∂H := by ring
    rw [h0] at hlim
    exact hlim.congr' hident
  have plane_ball : ∀ (P : Submodule ℝ (Amb n ℓ)) (hP : Module.finrank ℝ P = n) (t : ℝ) (ht : 0 ≤ t),
      ((μHE[n] : Measure (Amb n ℓ)).restrict (P : Set (Amb n ℓ))) (closedBall 0 t) = ENNReal.ofReal (unitBallVolume n * t ^ n) := by
    intro P hP t ht
    have : Nontrivial P := Module.nontrivial_of_finrank_pos (by rw [hP]; omega)
    have hrange : range (P.subtypeₗᵢ : P → Amb n ℓ) = (P : Set (Amb n ℓ)) := by ext x; simp
    rw [← hrange, ← P.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure,
      Measure.map_apply P.subtypeₗᵢ.continuous.measurable measurableSet_closedBall]
    have hpre : (P.subtypeₗᵢ : P → Amb n ℓ) ⁻¹' closedBall (0 : Amb n ℓ) t = closedBall (0 : P) t := by
      ext x
      simp [mem_closedBall, dist_eq_norm]
    have hHP : (μHE[n] : Measure P) = volume := by
      have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := P)
      rwa [hP] at this
    rw [hpre, hHP, InnerProductSpace.volume_closedBall, hP, ← ENNReal.ofReal_pow ht,
      ← ENNReal.ofReal_mul (pow_nonneg ht _)]
    congr 1
    rw [unitBallVolume, mul_comm]
    congr 2
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    ring
  have cutoff_exists : ∀ (a b : ℝ) (ha : 0 < a) (hab : a < b),
      ∃ c : C_c(Amb n ℓ, ℝ), (∀ y, 0 ≤ c y ∧ c y ≤ 1) ∧ (∀ y, ‖y‖ ≤ a → c y = 1) ∧ (∀ y, b ≤ ‖y‖ → c y = 0) := by
    intro a b ha hab
    have hba : 0 < b - a := sub_pos.2 hab
    refine ⟨⟨⟨fun y => min 1 (max 0 ((b - ‖y‖) / (b - a))), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall (0 : Amb n ℓ) b) fun y hy => ?_⟩, ?_, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, not_le] at hy
      have : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le
      simp [max_eq_left this]
    · intro y
      exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    · intro y hy
      have : 1 ≤ (b - ‖y‖) / (b - a) := by rw [le_div_iff₀ hba]; linarith
      show min 1 (max 0 ((b - ‖y‖) / (b - a))) = 1
      rw [max_eq_right (by linarith), min_eq_left this]
    · intro y hy
      have : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le
      show min 1 (max 0 ((b - ‖y‖) / (b - a))) = 0
      rw [max_eq_left this, min_eq_right zero_le_one]
  have density_of_tangent : ∀ (x : Amb n ℓ) (hxM : x ∈ V.carrier) (P : Submodule ℝ (Amb n ℓ)) (hP : Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P),
      V.HasDensity x (V.mult x) := by
    intro x hxM P hP
    have hrsod := Submission.rsod_blowUp_setIntegral_eq
    set H : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)) with hH
    set μ : Measure (Amb n ℓ) := V.weight with hμ
    have hη : ∀ (x : Amb n ℓ) (r : ℝ) (y : Amb n ℓ),
        Poincare.SimonGMT.Chapter03.blowUpMap x r y = r⁻¹ • (y - x) := fun _ _ _ => rfl
    have hweight : ∀ g : Amb n ℓ → ℝ, ∫ z, g z ∂μ = ∫ z in V.carrier, g z * V.mult z ∂H := by
      intro g
      rw [hμ, RectifiableVarifold.weight, integral_withDensity_eq_integral_toReal_smul₀
        V.aemeasurable_mult.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem₀ V.nullMeasurableSet_carrier] with z hz
      rw [ENNReal.toReal_ofReal (V.mult_pos z hz).le, smul_eq_mul, mul_comm]
    set ω : ℝ := unitBallVolume n with hωdef
    have hω : 0 < ω :=
      div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
    set θx : ℝ := V.mult x with hθxdef
    have hθx : 0 < θx := V.mult_pos x hxM
    have hPn : Module.finrank ℝ P = n := hP.1
    -- local finiteness of `μ_V` near `x`
    obtain ⟨δ₀, hδ₀, hδ₀U⟩ : ∃ δ > 0, closedBall x δ ⊆ U :=
      nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds (V.carrier_subset hxM))
    have hμfin : ∀ t : ℝ, t ≤ δ₀ → μ (closedBall x t) < ⊤ := by
      intro t ht
      calc μ (closedBall x t) ≤ μ (closedBall x δ₀) := measure_mono (closedBall_subset_closedBall ht)
        _ = ∫⁻ z in closedBall x δ₀, ENNReal.ofReal (V.mult z) ∂(H.restrict V.carrier) := by
            rw [hμ, RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall]
        _ = ∫⁻ z in V.carrier ∩ closedBall x δ₀, ENNReal.ofReal (V.mult z) ∂H := by
            rw [Measure.restrict_restrict measurableSet_closedBall, inter_comm]
        _ < ⊤ := (V.integrableOn_mult _ (isCompact_closedBall x δ₀) hδ₀U).lintegral_lt_top
    -- rescaled cutoff integrals converge
    have hlimc : ∀ c : C_c(Amb n ℓ, ℝ), Tendsto (fun r : ℝ => (r ^ n)⁻¹ *
        ∫ z, c (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂μ) (𝓝[>] 0)
        (𝓝 (θx * ∫ y in (P : Set (Amb n ℓ)), c y ∂H)) := by
      intro c
      refine (hP.2 c).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [hrsod n ℓ V.carrier c V.mult x r hr, hweight]
    -- integrability of a cutoff with support in `B_s`
    have hcint : ∀ (c : C_c(Amb n ℓ, ℝ)) (s : ℝ), 0 < s → (∀ y, s ≤ ‖y‖ → c y = 0) →
        (∀ y, 0 ≤ c y ∧ c y ≤ 1) → ∀ r : ℝ, 0 < r → s * r ≤ δ₀ →
        Integrable (fun z => c (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) μ := by
      intro c s hs hcs hc01 r hr hsr
      refine (Measure.integrableOn_of_bounded (s := closedBall x (s * r)) (hμfin _ hsr).ne
        (by simp only [hη]; fun_prop : Continuous fun z =>
          c (Poincare.SimonGMT.Chapter03.blowUpMap x r z)).aestronglyMeasurable
        (M := 1) (Eventually.of_forall fun z => ?_)).integrable_of_forall_notMem_eq_zero ?_
      · rw [Real.norm_of_nonneg (hc01 _).1]; exact (hc01 _).2
      · intro z hz
        apply hcs
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        rw [hη, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le, ← div_eq_inv_mul, le_div_iff₀ hr]
        exact hz.le
    -- integrability of cutoffs on the plane
    have hPint : ∀ (c : C_c(Amb n ℓ, ℝ)) (s : ℝ), 0 < s → (∀ y, s ≤ ‖y‖ → c y = 0) →
        (∀ y, 0 ≤ c y ∧ c y ≤ 1) → Integrable c (H.restrict (P : Set (Amb n ℓ))) := by
      intro c s hs hcs hc01
      refine (Measure.integrableOn_of_bounded (s := closedBall (0 : Amb n ℓ) s)
        (by rw [plane_ball P hPn s hs.le]; exact ENNReal.ofReal_ne_top)
        c.continuous.aestronglyMeasurable (M := 1)
        (Eventually.of_forall fun y => ?_)).integrable_of_forall_notMem_eq_zero ?_
      · exact (show ‖c y‖ ≤ 1 by rw [Real.norm_of_nonneg (hc01 y).1]; exact (hc01 y).2)
      · intro y hy
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact hcs y hy.le
    have hPreal : ∀ t : ℝ, 0 ≤ t → (H.restrict (P : Set (Amb n ℓ))).real (closedBall 0 t) = ω * t ^ n := by
      intro t ht
      rw [measureReal_def, plane_ball P hPn t ht, ENNReal.toReal_ofReal (by positivity)]
    have hindP : ∀ t : ℝ, 0 ≤ t → Integrable ((closedBall (0 : Amb n ℓ) t).indicator (fun _ => (1 : ℝ)))
        (H.restrict (P : Set (Amb n ℓ))) := by
      intro t ht
      rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [plane_ball P hPn t ht]; exact ENNReal.ofReal_ne_top
    have hindμ : ∀ r : ℝ, r ≤ δ₀ → Integrable ((closedBall x r).indicator (fun _ => (1 : ℝ))) μ := by
      intro r hr
      rw [integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const (hμfin r hr).ne
    have hφ : Tendsto (fun t : ℝ => θx * (ω * t ^ n)) (𝓝 1) (𝓝 (θx * ω)) := by
      have := (((continuous_pow n).tendsto (1 : ℝ)).const_mul ω).const_mul θx
      simpa using this
    have hreal : Tendsto (fun r : ℝ => (r ^ n)⁻¹ * μ.real (closedBall x r)) (𝓝[>] 0)
        (𝓝 (θx * ω)) := by
      rw [tendsto_order]
      constructor
      · intro a ha
        obtain ⟨t, ht1, ht2⟩ : ∃ t, t ∈ Ioo (1 / 2 : ℝ) 1 ∧ a < θx * (ω * t ^ n) :=
          ((show ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (1 / 2 : ℝ) 1 from
            Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)).and
            ((hφ.eventually (lt_mem_nhds ha)).filter_mono nhdsWithin_le_nhds)).exists
        have ht0 : 0 < t := by linarith [ht1.1]
        obtain ⟨c, hc01, hc1, hc0⟩ := cutoff_exists t 1 ht0 ht1.2
        have hPc : ω * t ^ n ≤ ∫ y in (P : Set (Amb n ℓ)), c y ∂H := by
          rw [← hPreal t ht0.le, ← integral_indicator_one measurableSet_closedBall]
          refine integral_mono (hindP t ht0.le) (hPint c 1 one_pos hc0 hc01) fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Amb n ℓ) t
          · rw [Set.indicator_of_mem hy, Pi.one_apply,
              hc1 y (by rwa [mem_closedBall, dist_zero_right] at hy)]
          · rw [Set.indicator_of_notMem hy]; exact (hc01 y).1
        have hev := (tendsto_order.1 (hlimc c)).1 a
          (lt_of_lt_of_le ht2 (mul_le_mul_of_nonneg_left hPc hθx.le))
        filter_upwards [hev, Ioo_mem_nhdsGT hδ₀] with r hr1 hr2
        refine lt_of_lt_of_le hr1 (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (pow_nonneg hr2.1.le n)))
        rw [← integral_indicator_one measurableSet_closedBall]
        refine integral_mono (hcint c 1 one_pos hc0 hc01 r hr2.1 (by linarith [hr2.2]))
          (hindμ r hr2.2.le) fun z => ?_
        by_cases hz : z ∈ closedBall x r
        · rw [Set.indicator_of_mem hz, Pi.one_apply]; exact (hc01 _).2
        · rw [Set.indicator_of_notMem hz]
          refine (hc0 _ ?_).le
          rw [mem_closedBall, dist_eq_norm, not_le] at hz
          rw [hη, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr2.1).le, ← div_eq_inv_mul,
            le_div_iff₀ hr2.1, one_mul]
          exact hz.le
      · intro b hb
        obtain ⟨s, hs1, hs2⟩ : ∃ s, s ∈ Ioo (1 : ℝ) 2 ∧ θx * (ω * s ^ n) < b :=
          ((show ∀ᶠ s in 𝓝[>] (1 : ℝ), s ∈ Ioo (1 : ℝ) 2 from
            Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)).and
            ((hφ.eventually (gt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds)).exists
        have hs0 : 0 < s := by linarith [hs1.1]
        obtain ⟨c, hc01, hc1, hc0⟩ := cutoff_exists 1 s one_pos hs1.1
        have hPc : ∫ y in (P : Set (Amb n ℓ)), c y ∂H ≤ ω * s ^ n := by
          rw [← hPreal s hs0.le, ← integral_indicator_one measurableSet_closedBall]
          refine integral_mono (hPint c s hs0 hc0 hc01) (hindP s hs0.le) fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Amb n ℓ) s
          · rw [Set.indicator_of_mem hy, Pi.one_apply]; exact (hc01 y).2
          · rw [Set.indicator_of_notMem hy]
            refine (hc0 y ?_).le
            rw [mem_closedBall, dist_zero_right, not_le] at hy
            exact hy.le
        have hev := (tendsto_order.1 (hlimc c)).2 b
          (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hPc hθx.le) hs2)
        filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < δ₀ / 2 by positivity)] with r hr1 hr2
        refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (pow_nonneg hr2.1.le n))) hr1
        rw [← integral_indicator_one measurableSet_closedBall]
        refine integral_mono (hindμ r (by linarith [hr2.2]))
          (hcint c s hs0 hc0 hc01 r hr2.1 (by nlinarith [hr2.2, hr2.1, hs1.2])) fun z => ?_
        by_cases hz : z ∈ closedBall x r
        · rw [Set.indicator_of_mem hz, Pi.one_apply, hc1]
          rw [mem_closedBall, dist_eq_norm] at hz
          rw [hη, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr2.1).le, ← div_eq_inv_mul,
            div_le_one hr2.1]
          exact hz
        · rw [Set.indicator_of_notMem hz]; exact (hc01 _).1
    have h2 := hreal.div_const ω
    rw [mul_div_assoc, div_self hω.ne', mul_one] at h2
    refine (ENNReal.tendsto_ofReal h2).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ₀] with r hr
    have hfin := hμfin r hr.2.le
    rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_div_of_pos (mul_pos hω (pow_pos hr.1 n)),
      measureReal_def]
    congr 1
    field_simp
  have Phi_measurable : Measurable (fun L : Rn n →L[ℝ] Amb n ℓ => L ∘L (Ring.inverse ((ContinuousLinearMap.adjoint L) ∘L L)) ∘L (ContinuousLinearMap.adjoint L)) := by
    classical
    have hinv : Measurable (Ring.inverse : (Rn n →L[ℝ] Rn n) → (Rn n →L[ℝ] Rn n)) := by
      have h := ContinuousOn.measurable_piecewise (s := {x : Rn n →L[ℝ] Rn n | IsUnit x})
        (f := Ring.inverse) (g := Ring.inverse)
        (fun x hx => by
          have := NormedRing.inverse_continuousAt (hx : IsUnit x).unit
          rw [IsUnit.unit_spec] at this
          exact this.continuousWithinAt)
        ((continuousOn_const (c := (0 : Rn n →L[ℝ] Rn n))).congr fun x hx =>
          Ring.inverse_non_unit x hx)
        Units.isOpen.measurableSet
      rwa [Set.piecewise_same] at h
    have hadj : Continuous (fun L : Rn n →L[ℝ] Amb n ℓ => ContinuousLinearMap.adjoint L) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn n) (F := Amb n ℓ)).continuous
    have hcomp : Continuous (fun p : (Rn n →L[ℝ] Amb n ℓ) × (Rn n →L[ℝ] Rn n) ×
        (Amb n ℓ →L[ℝ] Rn n) => p.1 ∘L p.2.1 ∘L p.2.2) := by
      exact continuous_fst.clm_comp (continuous_snd.fst.clm_comp continuous_snd.snd)
    have hm : Measurable (fun L : Rn n →L[ℝ] Amb n ℓ =>
        (L, Ring.inverse ((ContinuousLinearMap.adjoint L) ∘L L), ContinuousLinearMap.adjoint L)) :=
      measurable_id.prodMk ((hinv.comp (hadj.clm_comp continuous_id).measurable).prodMk
        hadj.measurable)
    exact hcomp.measurable.comp hm
  have Phi_eq : ∀ (L : Rn n →L[ℝ] Amb n ℓ) (hL : Function.Injective L),
      (LinearMap.range (L : Rn n →ₗ[ℝ] Amb n ℓ)).starProjection = L ∘L (Ring.inverse ((ContinuousLinearMap.adjoint L) ∘L L)) ∘L (ContinuousLinearMap.adjoint L) := by
    intro L hL
    set G : Rn n →L[ℝ] Rn n := (ContinuousLinearMap.adjoint L) ∘L L with hG
    have hGinj : Function.Injective G := by
      intro c d hcd
      have h1 : G (c - d) = 0 := by rw [map_sub, hcd, sub_self]
      have h2 : inner ℝ (L (c - d)) (L (c - d)) = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left]
        change inner ℝ (G (c - d)) (c - d) = 0
        rw [h1, inner_zero_left]
      rw [inner_self_eq_zero] at h2
      exact sub_eq_zero.1 (hL (by rw [h2, map_zero]))
    have hGunit : IsUnit G := by
      let e : Rn n ≃L[ℝ] Rn n :=
        (LinearEquiv.ofInjectiveEndo (G : Rn n →ₗ[ℝ] Rn n) hGinj).toContinuousLinearEquiv
      have he : (e : Rn n →L[ℝ] Rn n) = G := by ext c; rfl
      refine ⟨⟨G, (e.symm : Rn n →L[ℝ] Rn n), ?_, ?_⟩, rfl⟩
      · rw [← he]; ext c; simp
      · rw [← he]; ext c; simp
    have hGG : G ∘L Ring.inverse G = 1 := Ring.mul_inverse_cancel G hGunit
    refine ContinuousLinearMap.ext fun u => ?_
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨_, rfl⟩
    · rintro w ⟨c, rfl⟩
      rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_inner_left, map_sub]
      have h3 : (ContinuousLinearMap.adjoint L) ((L ∘L Ring.inverse G ∘L
          ContinuousLinearMap.adjoint L) u) = (ContinuousLinearMap.adjoint L) u := by
        have := congrArg (fun T : Rn n →L[ℝ] Rn n => T ((ContinuousLinearMap.adjoint L) u)) hGG
        simpa [hG] using this
      rw [h3, sub_self, inner_zero_left]
  set H : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)) with hH
  have hHRn : (μHE[n] : Measure (Rn n)) = volume := by
    have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Rn n)
    rwa [finrank_euclideanSpace_fin] at this
  -- (UD) in the `r⁻ⁿ` form
  have ud_tendsto : ∀ (ν : Measure (Amb n ℓ)) (A : Set (Amb n ℓ)), NullMeasurableSet A ν →
      ν A < ∞ → ∀ᵐ x ∂H, x ∉ A →
        Tendsto (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) := by
    intro ν A hA hfin
    have h0 := Submission.upperDensity_ne_zero_outside_hausdorff_null ν A hA hfin
    rw [measure_eq_zero_iff_ae_notMem] at h0
    have hω : 0 < unitBallVolume n :=
      div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
    filter_upwards [h0] with x hx hxA
    have hls : limsup (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
        (𝓝[>] 0) = 0 := by
      by_contra hne
      exact hx ⟨hxA, hne⟩
    have hq : Tendsto (fun r : ℝ => ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
        (𝓝[>] 0) (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      have hlt : limsup (fun r : ℝ => ν (A ∩ closedBall x r) /
          ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) < ε := by
        rw [hls]; exact hε
      exact (eventually_lt_of_limsup_lt hlt).mono fun r hr => hr.le
    have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (unitBallVolume n) *
        (ν (A ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hq (Or.inr ENNReal.ofReal_ne_top)
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [ENNReal.ofReal_mul hω.le, ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 hω).ne' ENNReal.ofReal_ne_top]
  -- `r⁻ⁿ μ_V(B_r(x) \ K) → 0` a.e. on a compact `K ⊆ M`
  have wdoc : ∀ Kset : Set (Amb n ℓ), IsCompact Kset → Kset ⊆ V.carrier →
      ∀ᵐ x ∂H, x ∈ Kset → Tendsto (fun r : ℝ => V.weight (closedBall x r \ Kset) /
        ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) := by
    intro Kset hK hKM
    obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU (hKM.trans V.carrier_subset)
    have hLc : IsCompact (cthickening δ Kset) := hK.cthickening
    set A : Set (Amb n ℓ) := (V.carrier \ Kset) ∩ cthickening δ Kset with hAdef
    have hac : V.weight ≪ H :=
      (withDensity_absolutelyContinuous _ _).trans
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    have hA : NullMeasurableSet A V.weight :=
      ((V.nullMeasurableSet_carrier.diff hK.isClosed.measurableSet.nullMeasurableSet).inter
        isClosed_cthickening.measurableSet.nullMeasurableSet).mono_ac hac
    have hAfin : V.weight A < ∞ := by
      calc V.weight A ≤ V.weight (cthickening δ Kset) := measure_mono inter_subset_right
        _ = ∫⁻ x in cthickening δ Kset, ENNReal.ofReal (V.mult x) ∂(H.restrict V.carrier) :=
            withDensity_apply _ isClosed_cthickening.measurableSet
        _ = ∫⁻ x in V.carrier ∩ cthickening δ Kset, ENNReal.ofReal (V.mult x) ∂H := by
            rw [Measure.restrict_restrict isClosed_cthickening.measurableSet, inter_comm]
        _ < ∞ := (V.integrableOn_mult _ hLc hδU).lintegral_lt_top
    have hMc : V.weight V.carrierᶜ = 0 := by
      have h1 : (H.restrict V.carrier) V.carrierᶜ = 0 :=
        ae_iff.1 (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
      exact withDensity_absolutelyContinuous _ _ h1
    filter_upwards [ud_tendsto V.weight A hA hAfin] with x hx hxK
    have hxA : x ∉ A := fun h => h.1.2 hxK
    refine (hx hxA).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    have hball : closedBall x r ⊆ cthickening δ Kset :=
      (closedBall_subset_closedBall hr.2.le).trans (closedBall_subset_cthickening hxK δ)
    have hset : A ∩ closedBall x r = (closedBall x r \ Kset) ∩ V.carrier := by
      ext y
      simp only [hAdef, mem_inter_iff, Set.mem_sdiff]
      constructor
      · rintro ⟨⟨⟨hyM, hyK⟩, _⟩, hyB⟩
        exact ⟨⟨hyB, hyK⟩, hyM⟩
      · rintro ⟨⟨hyB, hyK⟩, hyM⟩
        exact ⟨⟨⟨hyM, hyK⟩, hball hyB⟩, hyB⟩
    rw [hset, measure_inter_conull hMc]
  -- Lusin pieces
  -- Lusin pieces
  obtain ⟨Kp, hKc, hKM, hKcont, hKfin, hKnull⟩ := lusin_exhaustion
  -- the rectifiable cover
  obtain ⟨M₀, hM₀, F, hFlip, hcover⟩ := V.countablyRectifiable
  choose KF hKF using hFlip
  -- lower bounds for injective linear maps
  have hcLex : ∀ L : Rn n →L[ℝ] Amb n ℓ, ∃ c : ℝ≥0, 0 < c ∧
      (Function.Injective L → ∀ v, (c : ℝ) * ‖v‖ ≤ ‖L v‖) := by
    intro L
    by_cases hL : Function.Injective L
    · obtain ⟨K, hKpos, hK⟩ :=
        (LinearMap.injective_iff_antilipschitz (L : Rn n →ₗ[ℝ] Amb n ℓ)).1 hL
      refine ⟨K⁻¹, inv_pos.2 hKpos, fun _ v => ?_⟩
      have h1 := hK.le_mul_dist v 0
      simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at h1
      rw [NNReal.coe_inv, inv_mul_le_iff₀ (by exact_mod_cast hKpos)]
      exact h1
    · exact ⟨1, one_pos, fun h => absurd h hL⟩
  choose cL hcLpos hcL using hcLex
  -- the pieces of the parameter domains
  set s : ℕ → ℕ → Set (Rn n) := fun j k =>
    Poincare.SimonGMT.Chapter02.areaRegularSet (F j) ∩ ball 0 k with hsdef
  have hpart : ∀ j k, ∃ (t : ℕ → Set (Rn n)) (Lp : ℕ → Rn n →L[ℝ] Amb n ℓ),
      Pairwise (Function.onFun Disjoint t) ∧ (∀ i, MeasurableSet (t i)) ∧ (s j k ⊆ ⋃ i, t i) ∧
      (∀ i, ApproximatesLinearOn (F j) (Lp i) (s j k ∩ t i) (cL (Lp i) / 2)) ∧
      ((s j k).Nonempty → ∀ i, ∃ y ∈ s j k, Lp i = fderiv ℝ (F j) y) := fun j k =>
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F j) (s j k) (fderiv ℝ (F j))
      (fun x hx => hx.1.1.hasFDerivAt.hasFDerivWithinAt) (fun L => cL L / 2)
      (fun L => (div_pos (hcLpos L) two_pos).ne')
  choose t Lp _hdisj htm hcovt happ hact using hpart
  set A : ℕ → ℕ → ℕ → Set (Rn n) := fun j k i => s j k ∩ t j k i with hAdef
  have hAm : ∀ j k i, MeasurableSet (A j k i) := fun j k i =>
    ((Poincare.SimonGMT.Chapter02.measurableSet_areaRegularSet (F j)).inter measurableSet_ball).inter
      (htm j k i)
  have hAreg : ∀ j k i, ∀ a ∈ A j k i, DifferentiableAt ℝ (F j) a ∧
      Function.Injective (fderiv ℝ (F j) a) := fun j k i a ha => ha.1.1
  have hAbi : ∀ j k i, ∃ lam : ℝ, 0 < lam ∧ ∀ a ∈ A j k i, ∀ b ∈ A j k i,
      lam * ‖a - b‖ ≤ ‖F j a - F j b‖ := by
    intro j k i
    by_cases hne : (s j k).Nonempty
    · obtain ⟨y, hy, hLy⟩ := hact j k hne i
      have hinjL : Function.Injective (Lp j k i) := hLy ▸ hy.1.2
      refine ⟨(cL (Lp j k i) : ℝ) / 2, by have := hcLpos (Lp j k i); positivity,
        fun a ha b hb => ?_⟩
      have h1 := happ j k i a ha b hb
      have h2 := hcL (Lp j k i) hinjL (a - b)
      have h3 : ‖(Lp j k i) (a - b)‖ ≤ ‖F j a - F j b‖ +
          ‖F j a - F j b - (Lp j k i) (a - b)‖ := by
        have := norm_sub_le (F j a - F j b) (F j a - F j b - (Lp j k i) (a - b))
        rwa [sub_sub_cancel] at this
      push_cast at h1
      linarith
    · exact ⟨1, one_pos, fun a ha => absurd ⟨a, ha.1⟩ hne⟩
  choose lam hlam hbi using hAbi
  have hinj : ∀ j k i, InjOn (F j) (A j k i) := fun j k i b hb c hc h => by
    have h1 := hbi j k i b hb c hc
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖b - c‖ ≤ 0 := by nlinarith [norm_nonneg (b - c), hlam j k i]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  -- measurable inverses on the pieces
  have hGex : ∀ j k i, ∃ G : Amb n ℓ → Rn n, Measurable G ∧ ∀ a ∈ A j k i, G (F j a) = a := by
    intro j k i
    have hemb := ContinuousOn.measurableEmbedding (hAm j k i) (hKF j).continuous.continuousOn
      (hinj j k i)
    obtain ⟨G, hGm, hGeq⟩ := hemb.exists_measurable_extend (g := (Subtype.val : A j k i → Rn n))
      measurable_subtype_coe (fun _ => ⟨0⟩)
    exact ⟨G, hGm, fun a ha => congrFun hGeq ⟨a, ha⟩⟩
  choose G hGm hGa using hGex
  set Φ : (Rn n →L[ℝ] Amb n ℓ) → (Amb n ℓ →L[ℝ] Amb n ℓ) := fun L =>
    L ∘L (Ring.inverse ((ContinuousLinearMap.adjoint L) ∘L L)) ∘L (ContinuousLinearMap.adjoint L)
    with hΦ
  set T : ℕ → ℕ → ℕ → Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ) := fun j k i x =>
    Φ (fderiv ℝ (F j) (G j k i x)) with hTdef
  have hTm : ∀ j k i, Measurable (T j k i) := fun j k i =>
    Phi_measurable.comp ((measurable_fderiv ℝ (F j)).comp (hGm j k i))
  -- good points of each piece
  have hgood : ∀ m j k i, ∀ᵐ x ∂H, x ∈ Kp m ∩ F j '' A j k i →
      (∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P) ∧
      V.tangentProj x = T j k i x := by
    intro m j k i
    set S := F j '' A j k i with hSdef
    have hSm : MeasurableSet S :=
      (hAm j k i).image_of_continuousOn_injOn (hKF j).continuous.continuousOn (hinj j k i)
    have hSfin : H S < ⊤ := by
      calc H S ≤ (KF j : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) (A j k i) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              (hKF j).lipschitzOnWith
        _ < ⊤ := by
            rw [hHRn]
            exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
              ((measure_mono (inter_subset_left.trans inter_subset_right)).trans_lt
                measure_ball_lt_top)
    set J := Poincare.SimonGMT.Chapter02.areaJacobianAt (F j) with hJ
    have hgint := jac_integrableOn (F j) (hKF j) (A j k i) (hAm j k i) (hinj j k i)
    have hleb := leb_points ((A j k i).indicator J) hgint
    set N : Set (Rn n) := {a | ¬ ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ *
      ∫ y in closedBall a (ρ * r), ‖(A j k i).indicator J y - (A j k i).indicator J a‖)
        (𝓝[>] 0) (𝓝 0)} with hN
    have hN0 : volume N = 0 := ae_iff.1 hleb
    have hFN : H (F j '' N) = 0 := by
      have := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
        (A := N) n (hKF j).lipschitzOnWith
      rw [hHRn, hN0, mul_zero] at this
      exact le_antisymm this bot_le
    have hKS : H (Kp m \ S) < ⊤ := (measure_mono sdiff_subset).trans_lt (hKfin m)
    have hSK : H (S \ Kp m) < ⊤ := (measure_mono sdiff_subset).trans_lt hSfin
    filter_upwards [wdoc (Kp m) (hKc m) (hKM m),
      ud_tendsto H (Kp m \ S) ((hKc m).measurableSet.diff hSm).nullMeasurableSet hKS,
      ud_tendsto H (S \ Kp m) (hSm.diff (hKc m).measurableSet).nullMeasurableSet hSK,
      measure_eq_zero_iff_ae_notMem.1 hFN] with x hx3 hx4 hx5 hxN hxmem
    obtain ⟨hxK, a, ha, rfl⟩ := hxmem
    have hLeb : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ *
        ∫ y in closedBall a (ρ * r), ‖(A j k i).indicator J y - (A j k i).indicator J a‖)
          (𝓝[>] 0) (𝓝 0) := by
      by_contra h
      exact hxN ⟨a, h, rfl⟩
    set L := fderiv ℝ (F j) a with hL
    have hLinj : Function.Injective L := (hAreg j k i a ha).2
    set P : Submodule ℝ (Amb n ℓ) := LinearMap.range (L : Rn n →ₗ[ℝ] Amb n ℓ) with hPdef
    have hPset : (P : Set (Amb n ℓ)) = Set.range L := by
      rw [hPdef, LinearMap.coe_range, ContinuousLinearMap.coe_coe]
    have hPn : Module.finrank ℝ P = n :=
      (LinearMap.finrank_range_of_inj (f := (L : Rn n →ₗ[ℝ] Amb n ℓ)) hLinj).trans
        finrank_euclideanSpace_fin
    -- the density bound for `S`
    set c₁ : ℝ := (volume (closedBall (0 : Rn n) 1)).toReal with hc₁
    have hc₁0 : 0 ≤ c₁ := ENNReal.toReal_nonneg
    have hlam0 := hlam j k i
    set C : ℝ := (KF j : ℝ) ^ n * c₁ / lam j k i ^ n with hCdef
    have hC : 0 ≤ C := by positivity
    have hSball : ∀ r : ℝ, 0 < r → H (S ∩ closedBall (F j a) r) ≤ ENNReal.ofReal (C * r ^ n) := by
      intro r hr
      have hsub : S ∩ closedBall (F j a) r ⊆ F j '' (A j k i ∩ closedBall a (r / lam j k i)) := by
        rintro _ ⟨⟨b, hb, rfl⟩, hbr⟩
        refine ⟨b, ⟨hb, ?_⟩, rfl⟩
        rw [mem_closedBall, dist_eq_norm] at hbr ⊢
        have := hbi j k i b hb a ha
        rw [le_div_iff₀ hlam0, mul_comm]
        linarith
      have hvol1 : volume (closedBall (0 : Rn n) 1) = ENNReal.ofReal c₁ :=
        (ENNReal.ofReal_toReal measure_closedBall_lt_top.ne).symm
      have hval : (KF j : ℝ≥0∞) ^ n * (ENNReal.ofReal ((r / lam j k i) ^ n) * ENNReal.ofReal c₁) =
          ENNReal.ofReal (C * r ^ n) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_pow (NNReal.coe_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hCdef, div_pow]
        field_simp
      calc H (S ∩ closedBall (F j a) r) ≤ H (F j '' (A j k i ∩ closedBall a (r / lam j k i))) :=
            measure_mono hsub
        _ ≤ (KF j : ℝ≥0∞) ^ n *
              (μHE[n] : Measure (Rn n)) (A j k i ∩ closedBall a (r / lam j k i)) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              (hKF j).lipschitzOnWith
        _ ≤ (KF j : ℝ≥0∞) ^ n * volume (closedBall a (r / lam j k i)) := by
            rw [hHRn]; gcongr; exact inter_subset_right
        _ = ENNReal.ofReal (C * r ^ n) := by
            rw [Measure.addHaar_closedBall' volume a (div_pos hr hlam0).le,
              finrank_euclideanSpace_fin, hvol1, hval]
    have hW : Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
        (F j a) P := by
      refine weighted_tangent_at (Kp m) (hKc m) (hKM m) (hKcont m) (hKfin m) S hSm (F j a)
        hxK P hPn (fun f hfc hfs => ?_) C hC hSball (hx3 hxK)
        (hx4 fun h => h.2 ⟨a, ha, rfl⟩) (hx5 fun h => h.2 hxK)
      rw [hPset]
      exact blowup_area_tendsto (F j) (hKF j) (A j k i) (hAm j k i) hlam0 (hbi j k i) hgint ha
        (hAreg j k i a ha).1 hLinj hLeb f hfc hfs
    refine ⟨⟨P, hW⟩, ?_⟩
    have hex : ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
          (F j a) P := ⟨P, hW⟩
    have huniq : Classical.choose hex = P :=
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
        (V.mult_pos _ (hKM m hxK)).ne' (Classical.choose_spec hex) hW
    have hkey : ∀ Q : Submodule ℝ (Amb n ℓ), Q = P → Q.starProjection = P.starProjection := by
      rintro Q rfl; rfl
    rw [RectifiableVarifold.tangentProj, dif_pos hex, hkey _ huniq]
    refine (Phi_eq L hLinj).trans ?_
    simp only [hTdef, hΦ, hGa j k i a ha, hL]
  -- almost every point of the carrier lies in some piece
  have hcovae : ∀ᵐ x ∂(H.restrict V.carrier), ∃ m j k i, x ∈ Kp m ∩ F j '' A j k i := by
    have hN3 : ∀ j, H (F j '' (univ \ Poincare.SimonGMT.Chapter02.areaRegularSet (F j))) = 0 := by
      intro j
      have := Poincare.SimonGMT.Chapter02.area_image_compl_regularSet_eq_zero (hKF j) univ
      rwa [finrank_euclideanSpace_fin] at this
    have hnull : H ((V.carrier \ ⋃ m, Kp m) ∪ M₀ ∪
        ⋃ j, F j '' (univ \ Poincare.SimonGMT.Chapter02.areaRegularSet (F j))) = 0 :=
      measure_union_null (measure_union_null hKnull hM₀) (measure_iUnion_null hN3)
    rw [ae_restrict_iff'₀ V.nullMeasurableSet_carrier]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxM
    have hxK : ∃ m, x ∈ Kp m := by
      by_contra h
      push_neg at h
      exact hx (Or.inl (Or.inl ⟨hxM, by simpa using h⟩))
    obtain ⟨m, hm⟩ := hxK
    rcases hcover hxM with hx0 | hxr
    · exact absurd (Or.inl (Or.inr hx0)) hx
    obtain ⟨j, b, rfl⟩ := mem_iUnion.1 hxr
    have hb : b ∈ Poincare.SimonGMT.Chapter02.areaRegularSet (F j) := by
      by_contra h
      exact hx (Or.inr (mem_iUnion.2 ⟨j, b, ⟨mem_univ _, h⟩, rfl⟩))
    obtain ⟨k, hk⟩ := exists_nat_gt ‖b‖
    have hbs : b ∈ s j k := ⟨hb, by rwa [mem_ball, dist_zero_right]⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcovt j k hbs)
    exact ⟨m, j, k, i, hm, b, ⟨hbs, hi⟩, rfl⟩
  have hall : ∀ᵐ x ∂(H.restrict V.carrier), ∃ m j k i, x ∈ Kp m ∩ F j '' A j k i ∧
      (∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P) ∧
      V.tangentProj x = T j k i x := by
    have h1 : ∀ᵐ x ∂(H.restrict V.carrier), ∀ m j k i, x ∈ Kp m ∩ F j '' A j k i →
        (∃ P : Submodule ℝ (Amb n ℓ),
          Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P) ∧
        V.tangentProj x = T j k i x := by
      rw [ae_all_iff]; intro m
      rw [ae_all_iff]; intro j
      rw [ae_all_iff]; intro k
      rw [ae_all_iff]; intro i
      exact ae_restrict_of_ae (hgood m j k i)
    filter_upwards [h1, hcovae] with x hx1 hx2
    obtain ⟨m, j, k, i, hmem⟩ := hx2
    exact ⟨m, j, k, i, hmem, hx1 m j k i hmem⟩
  have hac : V.weight ≪ H.restrict V.carrier := withDensity_absolutelyContinuous _ _
  have hallμ := hac.ae_le hall
  have hmem : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
    hac.ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  have hacH : V.weight ≪ H :=
    hac.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have proj_congr : ∀ P Q : Submodule ℝ (Amb n ℓ), P = Q → P.starProjection = Q.starProjection := by
    rintro P Q rfl; rfl
  -- `p_x` is the projection onto any weighted approximate tangent plane at `x ∈ M`
  have tangentProj_eq : ∀ x ∈ V.carrier, ∀ P : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P →
      V.tangentProj x = P.starProjection := by
    intro x hxM P hW
    have hex : ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P :=
      ⟨P, hW⟩
    have huniq : Classical.choose hex = P :=
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
        (V.mult_pos _ hxM).ne' (Classical.choose_spec hex) hW
    rw [RectifiableVarifold.tangentProj, dif_pos hex, proj_congr _ _ huniq]
  -- good points of a globally bi-Lipschitz chart over a ball (rotated Lipschitz graphs)
  have graph_good : ∀ (G : Rn n → Amb n ℓ) (KG : ℝ≥0), LipschitzWith KG G →
      (∀ a b : Rn n, ‖a - b‖ ≤ ‖G a - G b‖) → ∀ (R : ℝ) (m : ℕ),
      ∀ᵐ x ∂H, x ∈ Kp m → ∀ a ∈ ball (0 : Rn n) R, G a = x → DifferentiableAt ℝ G a →
        Function.Injective (fderiv ℝ G a) →
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x
          (LinearMap.range (fderiv ℝ G a : Rn n →ₗ[ℝ] Amb n ℓ)) := by
    intro G KG hG hlow R m
    set A : Set (Rn n) := ball (0 : Rn n) R with hAdef
    have hAm : MeasurableSet A := measurableSet_ball
    have hbiA : ∀ a ∈ A, ∀ b ∈ A, (1 : ℝ) * ‖a - b‖ ≤ ‖G a - G b‖ := fun a _ b _ => by
      rw [one_mul]; exact hlow a b
    have hinjA : InjOn G A := fun b _ c _ h => by
      have h1 := hlow b c
      rw [h, sub_self, norm_zero] at h1
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
    set S := G '' A with hSdef
    have hSm : MeasurableSet S :=
      hAm.image_of_continuousOn_injOn hG.continuous.continuousOn hinjA
    have hSfin : H S < ⊤ := by
      calc H S ≤ (KG : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) A :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              hG.lipschitzOnWith
        _ < ⊤ := by
            rw [hHRn]
            exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) measure_ball_lt_top
    set J := Poincare.SimonGMT.Chapter02.areaJacobianAt G with hJ
    have hgint := jac_integrableOn G hG A hAm hinjA
    have hleb := leb_points (A.indicator J) hgint
    set N : Set (Rn n) := {a | ¬ ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ *
      ∫ y in closedBall a (ρ * r), ‖A.indicator J y - A.indicator J a‖)
        (𝓝[>] 0) (𝓝 0)} with hN
    have hN0 : volume N = 0 := ae_iff.1 hleb
    have hFN : H (G '' N) = 0 := by
      have := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
        (A := N) n hG.lipschitzOnWith
      rw [hHRn, hN0, mul_zero] at this
      exact le_antisymm this bot_le
    have hKS : H (Kp m \ S) < ⊤ := (measure_mono sdiff_subset).trans_lt (hKfin m)
    have hSK : H (S \ Kp m) < ⊤ := (measure_mono sdiff_subset).trans_lt hSfin
    filter_upwards [wdoc (Kp m) (hKc m) (hKM m),
      ud_tendsto H (Kp m \ S) ((hKc m).measurableSet.diff hSm).nullMeasurableSet hKS,
      ud_tendsto H (S \ Kp m) (hSm.diff (hKc m).measurableSet).nullMeasurableSet hSK,
      measure_eq_zero_iff_ae_notMem.1 hFN] with x hx3 hx4 hx5 hxN hxK a ha hGa hdiff hLinj
    subst hGa
    have hLeb : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ *
        ∫ y in closedBall a (ρ * r), ‖A.indicator J y - A.indicator J a‖)
          (𝓝[>] 0) (𝓝 0) := by
      by_contra h
      exact hxN ⟨a, h, rfl⟩
    set L := fderiv ℝ G a with hL
    set P : Submodule ℝ (Amb n ℓ) := LinearMap.range (L : Rn n →ₗ[ℝ] Amb n ℓ) with hPdef
    have hPset : (P : Set (Amb n ℓ)) = Set.range L := by
      rw [hPdef, LinearMap.coe_range, ContinuousLinearMap.coe_coe]
    have hPn : Module.finrank ℝ P = n :=
      (LinearMap.finrank_range_of_inj (f := (L : Rn n →ₗ[ℝ] Amb n ℓ)) hLinj).trans
        finrank_euclideanSpace_fin
    -- the density bound for `S`
    set c₁ : ℝ := (volume (closedBall (0 : Rn n) 1)).toReal with hc₁
    have hc₁0 : 0 ≤ c₁ := ENNReal.toReal_nonneg
    set C : ℝ := (KG : ℝ) ^ n * c₁ with hCdef
    have hC : 0 ≤ C := by positivity
    have hSball : ∀ r : ℝ, 0 < r → H (S ∩ closedBall (G a) r) ≤ ENNReal.ofReal (C * r ^ n) := by
      intro r hr
      have hsub : S ∩ closedBall (G a) r ⊆ G '' (A ∩ closedBall a r) := by
        rintro _ ⟨⟨b, hb, rfl⟩, hbr⟩
        refine ⟨b, ⟨hb, ?_⟩, rfl⟩
        rw [mem_closedBall, dist_eq_norm] at hbr ⊢
        exact (hlow b a).trans hbr
      have hvol1 : volume (closedBall (0 : Rn n) 1) = ENNReal.ofReal c₁ :=
        (ENNReal.ofReal_toReal measure_closedBall_lt_top.ne).symm
      have hval : (KG : ℝ≥0∞) ^ n * (ENNReal.ofReal (r ^ n) * ENNReal.ofReal c₁) =
          ENNReal.ofReal (C * r ^ n) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_pow (NNReal.coe_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hCdef]
        ring
      calc H (S ∩ closedBall (G a) r) ≤ H (G '' (A ∩ closedBall a r)) := measure_mono hsub
        _ ≤ (KG : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) (A ∩ closedBall a r) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              hG.lipschitzOnWith
        _ ≤ (KG : ℝ≥0∞) ^ n * volume (closedBall a r) := by
            rw [hHRn]; gcongr; exact inter_subset_right
        _ = ENNReal.ofReal (C * r ^ n) := by
            rw [Measure.addHaar_closedBall' volume a hr.le, finrank_euclideanSpace_fin, hvol1,
              hval]
    refine weighted_tangent_at (Kp m) (hKc m) (hKM m) (hKcont m) (hKfin m) S hSm (G a)
      hxK P hPn (fun f hfc hfs => ?_) C hC hSball (hx3 hxK)
      (hx4 fun h => h.2 ⟨a, ha, rfl⟩) (hx5 fun h => h.2 hxK)
    rw [hPset]
    exact blowup_area_tendsto G hG A hAm one_pos hbiA hgint ha hdiff hLinj hLeb f hfc hfs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (0) existence of the weighted approximate tangent plane
    filter_upwards [hallμ] with x hx
    obtain ⟨m, j, k, i, -, hex, -⟩ := hx
    exact hex
  · -- (1) tangent planes
    filter_upwards [hallμ] with x hx
    obtain ⟨m, j, k, i, -, hex, -⟩ := hx
    refine ⟨Classical.choose hex, (Classical.choose_spec hex).1, ?_⟩
    rw [RectifiableVarifold.tangentProj, dif_pos hex]
  · -- (2) measurability
    set Pc : ℕ × ℕ × ℕ × ℕ → Set (Amb n ℓ) := fun ι =>
      Kp ι.1 ∩ F ι.2.1 '' A ι.2.1 ι.2.2.1 ι.2.2.2 with hPc
    have hPcm : ∀ ι, MeasurableSet (Pc ι) := fun ι =>
      (hKc ι.1).measurableSet.inter ((hAm _ _ _).image_of_continuousOn_injOn
        (hKF _).continuous.continuousOn (hinj _ _ _))
    have hcovμ : ∀ᵐ x ∂V.weight, x ∈ ⋃ ι, Pc ι := by
      filter_upwards [hallμ] with x hx
      obtain ⟨m, j, k, i, hxm, -⟩ := hx
      exact mem_iUnion.2 ⟨(m, j, k, i), hxm⟩
    rw [← Measure.restrict_eq_self_of_ae_mem hcovμ, aestronglyMeasurable_iUnion_iff]
    rintro ⟨m, j, k, i⟩
    refine (hTm j k i).aestronglyMeasurable.congr ?_
    have hac' : V.weight.restrict (Pc (m, j, k, i)) ≪ H :=
      ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac).trans
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    filter_upwards [hac'.ae_le (hgood m j k i), ae_restrict_mem (hPcm (m, j, k, i))] with x hx hxP
    exact (hx hxP).2.symm
  · -- (3) density
    filter_upwards [hallμ, hmem] with x hx hxM
    obtain ⟨m, j, k, i, -, ⟨P, hP⟩, -⟩ := hx
    exact density_of_tangent x hxM P hP
  · -- (4) rotated Lipschitz graphs
    intro q f R L hfL
    obtain ⟨f', hf'L, hff'⟩ := hfL.extend_finite_dimension
    set K' : ℝ≥0 := lipschitzExtensionConstant (Rn ℓ) * L with hK'
    have hgp_sub : ∀ (a b : Rn n) (y z : Rn ℓ),
        graphPoint a y - graphPoint b z = graphPoint (a - b) (y - z) := by
      intro a b y z
      rw [rsod_graphPoint_eq_finAddEquivProd_symm, rsod_graphPoint_eq_finAddEquivProd_symm,
        rsod_graphPoint_eq_finAddEquivProd_symm, ← map_sub, Prod.mk_sub_mk]
    have hgp_norm : ∀ (a : Rn n) (y : Rn ℓ), ‖graphPoint a y‖ ^ 2 = ‖a‖ ^ 2 + ‖y‖ ^ 2 := by
      intro a y
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_add]
      simp [graphPoint]
    set G : Rn n → Amb n ℓ := fun w => q (graphPoint w (f' w)) with hGdef
    have hGsub : ∀ a b, G a - G b = q (graphPoint (a - b) (f' a - f' b)) := by
      intro a b
      simp only [hGdef, ← map_sub, hgp_sub]
    have hGlow : ∀ a b : Rn n, ‖a - b‖ ≤ ‖G a - G b‖ := by
      intro a b
      rw [hGsub, LinearIsometryEquiv.norm_map]
      have h := hgp_norm (a - b) (f' a - f' b)
      nlinarith [norm_nonneg (a - b), norm_nonneg (graphPoint (a - b) (f' a - f' b)),
        sq_nonneg ‖f' a - f' b‖]
    have hGlip : LipschitzWith (1 + K') G := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [dist_eq_norm, dist_eq_norm, hGsub, LinearIsometryEquiv.norm_map]
      have h := hgp_norm (a - b) (f' a - f' b)
      have h2 : ‖f' a - f' b‖ ≤ K' * ‖a - b‖ := by
        have := hf'L.dist_le_mul a b
        rwa [dist_eq_norm, dist_eq_norm] at this
      have h3 : ‖graphPoint (a - b) (f' a - f' b)‖ ≤ ‖a - b‖ + ‖f' a - f' b‖ := by
        nlinarith [norm_nonneg (a - b), norm_nonneg (graphPoint (a - b) (f' a - f' b)),
          norm_nonneg (f' a - f' b)]
      push_cast
      nlinarith
    have hgg : ∀ᵐ x ∂V.weight, ∀ m, x ∈ Kp m → ∀ a ∈ ball (0 : Rn n) R, G a = x →
        DifferentiableAt ℝ G a → Function.Injective (fderiv ℝ G a) →
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x
          (LinearMap.range (fderiv ℝ G a : Rn n →ₗ[ℝ] Amb n ℓ)) :=
      hacH.ae_le (ae_all_iff.2 fun m => graph_good G (1 + K') hGlip hGlow R m)
    filter_upwards [hgg, hallμ, hmem] with x hx hxall hxM x' hx' hxeq hdiff
    obtain ⟨m, j, k, i, ⟨hxm, -⟩, -⟩ := hxall
    have hev : f' =ᶠ[𝓝 x'] f := by
      filter_upwards [isOpen_ball.mem_nhds hx'] with w hw
      exact (hff' (ball_subset_closedBall hw)).symm
    have hdiff' : DifferentiableAt ℝ f' x' := hdiff.congr_of_eventuallyEq hev
    have hfd : fderiv ℝ f' x' = fderiv ℝ f x' := hev.fderiv_eq
    have hGx : G x' = x := by
      show q (graphPoint x' (f' x')) = x
      rw [← hff' (ball_subset_closedBall hx'), hxeq]
    -- the derivative of the graph map
    set DG : Rn n →L[ℝ] Amb n ℓ := (q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).comp
      (((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm :
        Rn n × Rn ℓ →L[ℝ] Amb n ℓ).comp
        ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ f x'))) with hDG
    have hGeq : G = fun w =>
        q ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm (w, f' w)) := by
      funext w
      simp only [hGdef, rsod_graphPoint_eq_finAddEquivProd_symm]
    have hGd : HasFDerivAt G DG x' := by
      rw [hGeq]
      have h1 : HasFDerivAt (fun w : Rn n => (w, f' w))
          ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ f x')) x' := by
        rw [← hfd]
        exact (hasFDerivAt_id x').prodMk hdiff'.hasFDerivAt
      exact q.toContinuousLinearEquiv.hasFDerivAt.comp x'
        ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm.hasFDerivAt.comp x' h1)
    have hDGv : ∀ v, DG v = q (graphPoint v (fderiv ℝ f x' v)) := by
      intro v
      rw [rsod_graphPoint_eq_finAddEquivProd_symm]
      rfl
    have hDGinj : Function.Injective DG := by
      intro v w hvw
      have h0 : DG (v - w) = 0 := by rw [map_sub, hvw, sub_self]
      rw [hDGv, LinearIsometryEquiv.map_eq_zero_iff] at h0
      have h := hgp_norm (v - w) (fderiv ℝ f x' (v - w))
      rw [h0, norm_zero] at h
      have h1 : ‖v - w‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖v - w‖, sq_nonneg ‖fderiv ℝ f x' (v - w)‖]
      exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1))
    have hW := hx m hxm x' hx' hGx hGd.differentiableAt (by rw [hGd.fderiv]; exact hDGinj)
    rw [hGd.fderiv] at hW
    rw [tangentProj_eq x hxM _ hW]
    refine proj_congr _ _ ?_
    have hfun : (fun v : Rn n => q (graphPoint v (fderiv ℝ f x' v))) =
        ⇑(DG : Rn n →ₗ[ℝ] Amb n ℓ) := by
      funext v
      rw [ContinuousLinearMap.coe_coe, hDGv]
    rw [hfun, ← LinearMap.coe_range, Submodule.span_eq]

/-- **Simon Ch. 4, 3.2–3.6 and 4.1–4.8** (monotonicity with `Lᵖ` mean curvature, `p > n`).  Let `V`
have generalized mean curvature `H` in `U`, `0 < R < S`, `B_S(y) ⊆ U`, `∫_{B_S(y)} |H|ᵖ dμ_V < ∞`
and `(R^{p−n} ∫_{B_R(y)} |H|ᵖ dμ_V)^{1/p} ≤ κΛ`, `κ = (p − n)/(4p)`, `Λ > 0`.  Then some `F` has
`e^{−Λ} ≤ F(r) ≤ e^Λ`, `|F(r) − 1| ≤ ½ e^{Λ/2} Λ (r/R)^{1−n/p}` (`≤ Λ (r/R)^{1−n/p}` if `Λ ≤ 1`)
for `0 < r ≤ R`, and `F(t) t⁻ⁿ μ_V(B_t(y)) + F(t) − 1` is nondecreasing on `(0, R]`.
Proof: `B_S(y)` is a compact subset of `U`, so `μ_V(B_S(y)) < ∞` and `H` is integrable there.  For
a `C¹` nonincreasing cutoff `φ`, the first variation of `φ(r/ρ)(x − y)`
(`aal_radial_first_variation_identity`) together with `φ' ≤ 0` and `|p_{T_x M} ν|² ∈ [0, 1]`
`μ_V`-a.e. (`ted_tangent_plane_facts`) gives
`∫ [n φ(r/ρ) + (r/ρ) φ'(r/ρ)] dμ_V ≤ −∫ φ(r/ρ) (x − y) · H dμ_V`; the cutoff limit, Hölder bound
and integrating factor for an abstract measure are `ted_lpm_abstract_monotonicity`. -/
theorem ted_lp_monotonicity : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R S Λ : ℝ), 0 < R → R < S → 0 < Λ → closedBall y S ⊆ U → ∫⁻ x in closedBall y S, ‖H x‖ₑ ^ p ∂V.weight < ⊤ → V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ F : ℝ → ℝ, (∀ r : ℝ, 0 < r → r ≤ R → Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (r / R) ^ (1 - (n : ℝ) / p) ∧ (Λ ≤ 1 → |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p))) ∧ ∀ s r : ℝ, 0 < s → s ≤ r → r ≤ R → F s * ((V.weight (closedBall y s)).toReal / s ^ n) + (F s - 1) ≤ F r * ((V.weight (closedBall y r)).toReal / r ^ n) + (F r - 1) := by
  intro n ℓ hn p hp U hU V H hH y R S Λ hR hRS hΛ hSU hHp hscaled
  -- Step 0(a): `p_x` is `μ_V`-a.e. the projection onto an `n`-plane, and `x ↦ p_x` is
  -- `μ_V`-a.e. strongly measurable (Simon Ch. 3, 1.9).
  obtain ⟨-, hP, hPm, -, -⟩ := ted_tangent_plane_facts n ℓ hn U hU V
  -- Step 0(b): `B_S(y)` is a compact subset of `U`, so `μ_V(B_S(y)) < ∞` and `H` is
  -- `μ_V`-integrable on `B_S(y)`.
  have hμS : V.weight (closedBall y S) < ⊤ := by
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact (V.integrableOn_mult _ (isCompact_closedBall y S) hSU).setLIntegral_lt_top
  have hHint : IntegrableOn H (closedBall y S) V.weight :=
    hH.1.integrableOn_compact_subset hSU (isCompact_closedBall y S)
  -- Step 2: the radial first-variation inequality (2.1), integrated.  Let `φ` be a `C¹`
  -- nonincreasing cutoff with `φ = 1` on `(-∞, 1]`, `φ = 0` on `[T, ∞)`, and `Tρ < S`.  The
  -- first-variation identity gives `∫ G dμ_V = -∫ φ(r/ρ) (x - y) · H dμ_V`, where
  -- `G = n φ(r/ρ) + (r/ρ) φ'(r/ρ) (1 - w)`, `w = |(x - y) - p_x(x - y)|²/r²`; since `φ' ≤ 0`
  -- and `0 ≤ w ≤ 1` `μ_V`-a.e., `n φ(r/ρ) + (r/ρ) φ'(r/ρ) ≤ G ≤ n φ(r/ρ)` `μ_V`-a.e.
  have hrad : ∀ (φ : ℝ → ℝ) (T ρ : ℝ), ContDiff ℝ 1 φ → Antitone φ →
      (∀ t : ℝ, t ≤ 1 → φ t = 1) → (∀ t : ℝ, T ≤ t → φ t = 0) → 0 < ρ → T * ρ < S →
      ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂V.weight ≤
        -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
    intro φ T ρ hφ hφa hφ1 hφT hρ hTρ
    have hBU : closedBall y (T * ρ) ⊆ U := (closedBall_subset_closedBall hTρ.le).trans hSU
    -- `φ` and `φ'` vanish on `(T, ∞)`, so the integrands vanish off `B_{Tρ}(y)`.
    have hφ'T : ∀ t, T < t → deriv φ t = 0 := by
      intro t ht
      rw [Filter.EventuallyEq.deriv_eq (f := fun _ => (0 : ℝ))
        (by filter_upwards [Ioi_mem_nhds ht] with s hs using hφT s hs.le)]
      exact deriv_const t 0
    have hfar : ∀ x : Amb n ℓ, T * ρ < ‖x - y‖ →
        φ (‖x - y‖ / ρ) = 0 ∧ deriv φ (‖x - y‖ / ρ) = 0 := by
      intro x hx
      have hT : T < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; exact hx
      exact ⟨hφT _ hT.le, hφ'T _ hT⟩
    -- A continuous function vanishing off `B_{Tρ}(y) ⊆ B_S(y)` is `μ_V`-integrable.
    have hint : ∀ g : Amb n ℓ → ℝ, Continuous g → (∀ x, T * ρ < ‖x - y‖ → g x = 0) →
        Integrable g V.weight := by
      intro g hg hg0
      obtain ⟨C, hC⟩ := (isCompact_closedBall y (T * ρ)).exists_bound_of_continuousOn
        hg.continuousOn
      have hgB : IntegrableOn g (closedBall y (T * ρ)) V.weight :=
        IntegrableOn.of_bound ((measure_mono (closedBall_subset_closedBall hTρ.le)).trans_lt hμS)
          hg.aestronglyMeasurable.restrict C
          ((ae_restrict_iff' measurableSet_closedBall).2 (ae_of_all _ hC))
      refine hgB.integrable_of_forall_notMem_eq_zero fun x hx => hg0 x ?_
      simpa [mem_closedBall, dist_eq_norm] using hx
    have hφc : Continuous φ := hφ.continuous
    have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
    have hrc : Continuous fun x : Amb n ℓ => ‖x - y‖ / ρ :=
      (continuous_sub_right y).norm.div_const ρ
    have hfint : Integrable (fun x => (n : ℝ) * φ (‖x - y‖ / ρ) +
        ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) V.weight :=
      hint _ ((continuous_const.mul (hφc.comp hrc)).add (hrc.mul (hφ'c.comp hrc)))
        fun x hx => by simp [(hfar x hx).1, (hfar x hx).2]
    have hnint : Integrable (fun x => (n : ℝ) * φ (‖x - y‖ / ρ)) V.weight :=
      hint _ (continuous_const.mul (hφc.comp hrc)) fun x hx => by simp [(hfar x hx).1]
    -- The integrand `G` of the first-variation identity is `μ_V`-a.e. strongly measurable.
    have hev : Continuous fun q : (Amb n ℓ →L[ℝ] Amb n ℓ) × Amb n ℓ => q.1 q.2 :=
      isBoundedBilinearMap_apply.continuous
    have hpv : AEStronglyMeasurable (fun x => V.tangentProj x (x - y)) V.weight :=
      hev.comp_aestronglyMeasurable (hPm.prodMk (continuous_sub_right y).aestronglyMeasurable)
    have hGm : AEStronglyMeasurable (fun x => (n : ℝ) * φ (‖x - y‖ / ρ) +
        ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) *
          (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) V.weight := by
      have hpv' := hpv.aemeasurable
      have hφm : Measurable φ := hφc.measurable
      have hφ'm : Measurable (deriv φ) := hφ'c.measurable
      apply AEMeasurable.aestronglyMeasurable
      fun_prop
    -- `(r/ρ) φ'(r/ρ) ≤ 0` and `w ≥ 0` everywhere, so the lower bound holds everywhere.
    have hlow : ∀ x : Amb n ℓ, (n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ≤
        (n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) *
          (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) := by
      intro x
      have hc : ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (div_nonneg (norm_nonneg _) hρ.le) hφa.deriv_nonpos
      have hw0 : 0 ≤ ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2 := by positivity
      have := mul_nonpos_of_nonpos_of_nonneg hc hw0
      rw [mul_sub, mul_one]
      linarith
    -- Where `p_x = p_P` (`μ_V`-a.e.), `(x - y) - p_x(x - y) = p_{P⊥}(x - y)`, so `w ≤ 1`.
    have hupp : ∀ᵐ x ∂V.weight, (n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) *
        (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) ≤
        (n : ℝ) * φ (‖x - y‖ / ρ) := by
      filter_upwards [hP] with x hx
      obtain ⟨P, -, hPx⟩ := hx
      have hc : ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (div_nonneg (norm_nonneg _) hρ.le) hφa.deriv_nonpos
      have hperp : (x - y) - P.starProjection (x - y) = Pᗮ.starProjection (x - y) := by
        rw [Submodule.starProjection_orthogonal']
        rfl
      have hw1 : ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2 ≤ 1 := by
        rw [hPx, hperp]
        exact div_le_one_of_le₀
          (pow_le_pow_left₀ (norm_nonneg _) (Pᗮ.norm_starProjection_apply_le _) 2) (sq_nonneg _)
      have := mul_nonpos_of_nonpos_of_nonneg hc (sub_nonneg.2 hw1)
      linarith
    have hGint : Integrable (fun x => (n : ℝ) * φ (‖x - y‖ / ρ) +
        ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) *
          (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) V.weight :=
      integrable_of_le_of_le hGm (ae_of_all _ hlow) hupp hfint hnint
    exact (integral_mono_ae hfint hGint (ae_of_all _ hlow)).trans_eq
      (aal_radial_first_variation_identity n ℓ U V H hH hP y φ T ρ hφ hφ1 hφT hρ hBU)
  -- Steps 1 and 3–5: the abstract monotonicity for `μ = μ_V`; `V.scaledLpNorm H p y R` is
  -- `(R^{p-n} ∫_{B_R(y)} |H|ᵖ dμ_V)^{1/p}` by definition.
  exact Submission.ted_lpm_abstract_monotonicity n ℓ hn p hp V.weight H y R S Λ hR hRS hΛ hμS
    hHint hHp hscaled hrad
/-- **Simon Ch. 4, 3.9–3.13, 4.9 and Remark 4.10(1)** under the Allard hypotheses 2.3: at every
`y ∈ spt V ∩ B̆_ρ(0)` the density is at least one, i.e. `μ_V(B_s(y)) ≥ (1 − ε) ω_n sⁿ` for all small
`s > 0`.  Proof: put `r = (ρ − |y|)/8`, `κ = (p − n)/(4p)`, `Λ = max(δ, 0)/κ + 1` and
`c(t) = ½ e^{Λ/2} Λ (t/r)^{1 − n/p}`.  For `μ_V`-a.e. `x ∈ B̆_r(y)` we have `B_{2r}(x) ⊆ B_ρ(0)`, so
the `Lᵖ` monotonicity `ted_lp_monotonicity` applies at `x` with radii `r < 2r`; with
`Θⁿ(μ_V, x) = θ(x) ≥ 1` (`ted_tangent_plane_facts` (3)) it gives
`ω_n ≤ (1 + c(t)) t⁻ⁿ μ_V(B_t(x)) + c(t)` on `(0, r]` (`ted_dge1_density_le_monotone_bound`).
As `y ∈ spt μ_V` and `μ_V(B_{2r}(y)) < ∞`, the upper-semicontinuity argument
`ted_dge1_support_density_lower_bound` transfers this to `y`. -/
theorem ted_density_ge_one : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), V.AllardHypotheses H p δ ρ → ∀ y ∈ V.support ∩ ball (0 : Amb n ℓ) ρ, ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((1 - ε) * (unitBallVolume n * s ^ n)) ≤ V.weight (closedBall y s) := by
  intro n ℓ hn p hp U hU V H δ ρ hA y hy ε hε
  obtain ⟨hρ, hH, hθ, -, hball0, -, hK0⟩ := hA
  have hysupp : y ∈ V.weight.support := (show y ∈ U ∩ V.weight.support from hy.1).2
  have hyρ : ‖y‖ < ρ := mem_ball_zero_iff.mp hy.2
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < p := lt_trans hn' hp
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  set d := ρ - ‖y‖ with hd_def
  have hd : 0 < d := by linarith
  set r := d / 8 with hr_def
  have hr : 0 < r := by positivity
  -- the balls `B_{2r}(x)`, `x ∈ B̆_r(y)`, stay inside `B_ρ(0) ⊆ U`
  have hsub0 : ∀ x : Amb n ℓ, x ∈ ball y r → closedBall x (2 * r) ⊆ closedBall (0 : Amb n ℓ) ρ := by
    intro x hx z hz
    rw [mem_ball] at hx
    rw [mem_closedBall] at hz
    have h1 : dist z 0 ≤ dist z x + (dist x y + dist y 0) :=
      (dist_triangle z x 0).trans (add_le_add le_rfl (dist_triangle x y 0))
    simp only [dist_zero_right] at h1
    rw [mem_closedBall, dist_zero_right]
    linarith
  -- (F2): `μ_V(B_{2r}(y)) < ∞`, as `B_{2r}(y)` is a compact subset of `U`
  have hfin2 : V.weight (closedBall y (2 * r)) < ⊤ := by
    have hKU : closedBall y (2 * r) ⊆ U := by
      intro z hz
      apply hball0
      rw [mem_closedBall] at hz ⊢
      have h1 := dist_triangle z y 0
      simp only [dist_zero_right] at h1 ⊢
      linarith
    have hKm : MeasurableSet (closedBall y (2 * r)) := measurableSet_closedBall
    unfold RectifiableVarifold.weight
    rw [withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_comm]
    exact (V.integrableOn_mult _ (isCompact_closedBall _ _) hKU).lintegral_lt_top
  -- (A): `∫_{B_ρ(0)} |H|ᵖ dμ_V < ∞`
  have hI0 : ∫⁻ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ₑ ^ p ∂V.weight < ⊤ := by
    have h1 : V.scaledLpNorm H p 0 ρ < ⊤ := lt_of_le_of_lt hK0 ENNReal.ofReal_lt_top
    unfold RectifiableVarifold.scaledLpNorm at h1
    have h2 := (ENNReal.rpow_lt_top_iff_of_pos (by positivity : (0 : ℝ) < 1 / p)).mp h1
    have ha : ENNReal.ofReal (ρ ^ (p - n)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.rpow_pos_of_pos hρ _
    rcases ENNReal.mul_lt_top_iff.mp h2 with h | h | h
    · exact h.2
    · exact absurd h ha
    · rw [h]
      exact ENNReal.zero_lt_top
  -- Step 1: the constants `κ`, `Λ` (so `δ ≤ κ Λ`), `A`, `β` and the error `c(t) = A (t/r)^β`
  set κ := (p - n) / (4 * p) with hκ_def
  have hκ : 0 < κ := div_pos (by linarith) (by linarith)
  set Λ := max δ 0 / κ + 1 with hΛ_def
  have hΛ : 0 < Λ := by positivity
  have hκΛ : δ ≤ κ * Λ := by
    have h1 : κ * (max δ 0 / κ) = max δ 0 := by field_simp
    have h2 : κ * Λ = max δ 0 + κ := by rw [hΛ_def, mul_add, h1, mul_one]
    have h3 := le_max_left δ 0
    linarith
  set A := Real.exp (Λ / 2) / 2 * Λ with hA_def
  have hA0 : 0 ≤ A := by positivity
  set β := 1 - (n : ℝ) / p with hβ_def
  have hβ : 0 < β := by
    have : (n : ℝ) / p < 1 := (div_lt_one hp0).mpr hp
    linarith
  set c : ℝ → ℝ := fun t => A * (t / r) ^ β with hc_def
  have hc0 : ∀ t : ℝ, 0 < t → t ≤ r → 0 ≤ c t := fun t ht _ =>
    mul_nonneg hA0 (Real.rpow_nonneg (div_nonneg ht.le hr.le) _)
  have hclim : Tendsto c (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => A * (t / r) ^ β) (𝓝 0) (𝓝 (A * ((0 : ℝ) / r) ^ β)) :=
      (((continuous_id.div_const r).tendsto 0).rpow_const (Or.inr hβ.le)).const_mul A
    rw [zero_div, Real.zero_rpow hβ.ne', mul_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  -- Steps 3 and 5: upper semicontinuity at the support point `y`
  refine Submission.ted_dge1_support_density_lower_bound n ℓ V.weight y (unitBallVolume n) r c hω hr
    hysupp hfin2 hc0 hclim ?_ ε hε
  -- Step 4: `Θⁿ(μ_V, x) = θ(x) ≥ 1` for `μ_V`-a.e. `x`
  have hts := (Submission.ted_tangent_plane_facts n ℓ hn U hU V).2.2.2.1
  filter_upwards [hts, hθ] with x hxd hx1 hxy t ht htr
  have hsubx : closedBall x (2 * r) ⊆ U := (hsub0 x hxy).trans hball0
  have hfin : ∫⁻ z in closedBall x (2 * r), ‖H z‖ₑ ^ p ∂V.weight < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set (hsub0 x hxy)) hI0
  -- (K-mono): `K(x, r) ≤ K(0, ρ) ≤ δ ≤ κ Λ`
  have hKx : V.scaledLpNorm H p x r ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) := by
    have hKmono : V.scaledLpNorm H p x r ≤ V.scaledLpNorm H p 0 ρ := by
      unfold RectifiableVarifold.scaledLpNorm
      apply ENNReal.rpow_le_rpow _ (by positivity)
      exact mul_le_mul'
        (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hr.le (by linarith) (by linarith)))
        (lintegral_mono_set ((closedBall_subset_closedBall (by linarith)).trans (hsub0 x hxy)))
    exact hKmono.trans (hK0.trans (ENNReal.ofReal_le_ofReal hκΛ))
  -- Step 2: the `Lᵖ` monotonicity at `x` with `R = r`, `S = 2r`
  obtain ⟨F, hF, hmono⟩ := Submission.ted_lp_monotonicity n ℓ hn p hp U hU V H hH x r (2 * r) Λ hr
    (by linarith) hΛ hsubx hfin hKx
  have key := Submission.ted_dge1_density_le_monotone_bound n ℓ V.weight x (unitBallVolume n) r A β
    (V.mult x) F hω hr hβ (by linarith) (fun t ht htr => (hF t ht htr).2.2.1) hmono hxd t ht htr
  have h1 : unitBallVolume n ≤ unitBallVolume n * V.mult x := le_mul_of_one_le_right hω.le hx1
  show unitBallVolume n ≤ (1 + c t) * ((V.weight (closedBall x t)).toReal / t ^ n) + c t
  simp only [hc_def]
  linarith

/-- **Simon Ch. 3, Remark 1.8(2)** via the Upper Density Theorem (Ch. 1, 3.6), on an open set `W`
of finite `μ_V`-mass: if every `y ∈ spt V ∩ W` satisfies `μ_V(B_s(y)) ≥ c ω_n sⁿ` for some `c > 0`
and all small `s > 0`, then `Hⁿ((spt V ∩ W) \ M) = 0`.  A measurable kernel `B ⊆ M` of the
`Hⁿ`-null-measurable carrier is `μ_V`-conull; at `x ∈ (spt V ∩ W) \ M` the upper density of
`μ_V ⌞ (B ∩ W)` is at least `c > 0` while `x ∉ B ∩ W`, so 3.6 makes these points `Hⁿ`-null. -/
theorem ted_adb_support_diff_carrier_null : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (W : Set (Amb n ℓ)), IsOpen W → V.weight W < ⊤ → (∀ y ∈ V.support ∩ W, ∃ c : ℝ, 0 < c ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * (unitBallVolume n * s ^ n)) ≤ V.weight (closedBall y s)) → (μHE[n] : Measure (Amb n ℓ)) ((V.support ∩ W) \ V.carrier) = 0 := by
  intro n ℓ U V W hWo hWfin hlow
  -- Step 1: `ω_n > 0`.
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  -- Step 2: a measurable kernel `B ⊆ M` with `B = M` `Hⁿ`-a.e.
  obtain ⟨B, hBM, hBmeas, hBae⟩ := V.nullMeasurableSet_carrier.exists_measurable_subset_ae_eq
  -- Step 3: `μ_V(Bᶜ) = Hⁿ ⌞ θ (Bᶜ ∩ M) = 0`, since `Hⁿ(M \ B) = 0`.
  have hBc : V.weight Bᶜ = 0 := by
    rw [RectifiableVarifold.weight, withDensity_apply _ hBmeas.compl]
    refine setLIntegral_measure_zero _ _ ?_
    rw [Measure.restrict_apply hBmeas.compl, inter_comm, ← Set.sdiff_eq]
    exact (ae_eq_set.1 hBae).2
  -- Step 4: the Upper Density Theorem for `ν = μ_V` and `A = B ∩ W`, with `μ_V(A) ≤ μ_V(W) < ∞`.
  have hE := upperDensity_ne_zero_outside_hausdorff_null V.weight (B ∩ W)
    (hBmeas.inter hWo.measurableSet).nullMeasurableSet
    ((measure_mono inter_subset_right).trans_lt hWfin)
  -- Steps 5–6: `(spt V ∩ W) \ M` lies in the exceptional set of 3.6.
  refine measure_mono_null (fun x hx => ?_) hE
  obtain ⟨⟨hxS, hxW⟩, hxM⟩ := hx
  -- (a) `x ∉ A`, as `A ⊆ B ⊆ M`.
  refine ⟨fun hxA => hxM (hBM hxA.1), ?_⟩
  obtain ⟨c, hc, hev⟩ := hlow x ⟨hxS, hxW⟩
  -- (b) `B_r(x) ⊆ W` for small `r > 0`, since `W` is open.
  have hloc : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall x r ⊆ W :=
    nhdsWithin_le_nhds (eventually_closedBall_subset (hWo.mem_nhds hxW))
  -- (c), (d) For small `r > 0`: `μ_V(A ∩ B_r(x)) = μ_V(B_r(x)) ≥ c ω_n rⁿ`.
  have hge : ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal c ≤
      V.weight ((B ∩ W) ∩ closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n) := by
    filter_upwards [hev, hloc, self_mem_nhdsWithin] with r hr hrW hr0
    have hpos : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr0 n)
    have hset : (B ∩ W) ∩ closedBall x r = closedBall x r ∩ B := by
      ext z
      exact ⟨fun hz => ⟨hz.2, hz.1.1⟩, fun hz => ⟨⟨hz.2, hrW hz.1⟩, hz.1⟩⟩
    rw [hset, measure_inter_conull hBc,
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hpos).ne')
        (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul hc.le]
    exact hr
  -- (e) Hence the limsup is at least `ofReal c > 0`.
  exact ((ENNReal.ofReal_pos.2 hc).trans_le (le_limsup_of_frequently_le hge.frequently)).ne'
/-- **Simon Ch. 5, 2.4** (mass, multiplicity and carrier bounds under the hypotheses 2.3), with the
explicit constants `C, δP` of `ted_adb_constants` for `κ = (p − n)/(4p)` and `ω = ω_n`.  For
`|y| ≤ 3δρ` the monotonicity `ted_lp_monotonicity` applies with `Λ = δ/κ ≤ 1` on `(0, R]`,
`R = (1 − 4δ)ρ ≥ ρ/2`, inside `B_{(1−3δ)ρ}(y) ⊆ B_ρ(0)` (`aal_allard_subball_bounds`):
`Φ(t) = F(t) t⁻ⁿ μ(B_t(y)) + F(t) − 1` is nondecreasing, `e^{−Λ} ≤ F ≤ e^Λ` and `|F − 1| ≤ Λ`.
(i) `Φ(s) ≤ Φ(R)` and `R⁻ⁿ μ(B_R(y)) ≤ (1 + δ)(1 − 4δ)⁻ⁿ ω_n` give
`s⁻ⁿ μ(B_s(y)) ≤ e^{2Λ}(1 + δ)(1 − 4δ)⁻ⁿ ω_n + 2e^Λ Λ ≤ (1 + Cδ) ω_n`.
(ii) For `y ∈ spt V`, `Φ ≥ ω_n` on `(0, R]` (`aal_monotone_quantity_ge_density` with
`ted_density_ge_one`), so `s⁻ⁿ μ(B_s(y)) ≥ e^{−Λ}(ω_n − Λ) ≥ (1 − Cδ) ω_n`.
(iii) `Θⁿ(μ_V, x) = θ(x)` `μ_V`-a.e. (`ted_tangent_plane_facts`) and (i) give `θ ≤ 1 + Cδ`.
(iv) The upper density theorem (`ted_adb_support_diff_carrier_null` on `B̆_ρ(0)`), with the lower
density bound `ted_density_ge_one` at `ε = 1/2`. -/
theorem ted_allard_density_bounds : ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C δP : ℝ, 1 ≤ C ∧ 0 < δP ∧ δP ≤ 1 / 8 ∧ C * δP ≤ 1 / 2 ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δP → V.AllardHypotheses H p δ ρ → (∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → V.weight (closedBall y s) ≤ ENNReal.ofReal ((1 + C * δ) * (unitBallVolume n * s ^ n))) ∧ (∀ y ∈ V.support, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → ENNReal.ofReal ((1 - C * δ) * (unitBallVolume n * s ^ n)) ≤ V.weight (closedBall y s)) ∧ (∀ᵐ x ∂V.weight, ‖x‖ ≤ 3 * δ * ρ → V.mult x ≤ 1 + C * δ) ∧ (μHE[n] : Measure (Amb n ℓ)) ((V.support ∩ ball 0 ρ) \ V.carrier) = 0 := by
  intro n ℓ hn p hp
  have hp0 : 0 < p := (Nat.cast_nonneg n).trans_lt hp
  -- `κ = (p − n)/(4p) > 0`, the Hölder exponent `1 − n/p > 0` and `ω_n > 0`.
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, (p - n) / (4 * p) = κ := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [← hκdef]
    exact div_pos (sub_pos.2 hp) (by linarith)
  have hα : 0 < 1 - (n : ℝ) / p := sub_pos.2 ((div_lt_one hp0).2 hp)
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  obtain ⟨C, δP, hC1, hδP0, hδP8, hδPκ, hCδP, hCbd⟩ :=
    Submission.ted_adb_constants n κ (unitBallVolume n) hκ hω
  refine ⟨C, δP, hC1, hδP0, hδP8, hCδP, ?_⟩
  intro U hU V H δ ρ hδ hδP hA
  obtain ⟨hρ, hHMC, -, -, -, hmass, -⟩ := id hA
  have hδ8 : δ ≤ 1 / 8 := hδP.trans hδP8
  have hCδ : 0 ≤ C * δ := mul_nonneg (zero_le_one.trans hC1) hδ.le
  -- `Λ = δ/κ ∈ (0, 1]` with `κ Λ = δ`; the two elementary bounds of `ted_adb_constants` at `t = δ`.
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, δ / κ = Λ := ⟨_, rfl⟩
  have hΛ : 0 < Λ := by
    rw [← hΛdef]
    exact div_pos hδ hκ
  have hΛ1 : Λ ≤ 1 := by
    rw [← hΛdef]
    exact (div_le_one hκ).2 (hδP.trans hδPκ)
  have hκΛ : (p - n) / (4 * p) * Λ = δ := by
    rw [hκdef, ← hΛdef]
    field_simp
  obtain ⟨hP, hM⟩ := hCbd δ hδ hδP
  rw [hΛdef] at hP hM
  -- Radii `R = (1 − 4δ)ρ ∈ [ρ/2, S)` and `S = (1 − 3δ)ρ`; for `|y| ≤ 3δρ` and `r ≤ S`,
  -- `B_r(y) ⊆ B_ρ(0)`, so `μ_V(B_r(y)) ≤ μ_V(B_ρ(0)) < ∞`.
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, (1 - 4 * δ) * ρ = R := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, (1 - 3 * δ) * ρ = S := ⟨_, rfl⟩
  have hδρ : 0 < δ * ρ := mul_pos hδ hρ
  have hδρ8 : δ * ρ ≤ 1 / 8 * ρ := mul_le_mul_of_nonneg_right hδ8 hρ.le
  have h3δρ : 3 * δ * ρ = 3 * (δ * ρ) := by ring
  have hR' : R = ρ - 4 * (δ * ρ) := by rw [← hRdef]; ring
  have hS' : S = ρ - 3 * (δ * ρ) := by rw [← hSdef]; ring
  have hR : 0 < R := by linarith
  have hRS : R < S := by linarith
  have hρR : ρ / 2 ≤ R := by linarith
  have hS : 0 < S := by linarith
  have hSρ : S ≤ ρ := by linarith
  have hRρ : R ≤ ρ := by linarith
  have hball : ∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ r : ℝ, r ≤ S →
      closedBall y r ⊆ closedBall 0 ρ :=
    fun y hy r hr => closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith)
  have hfin : ∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ r : ℝ, r ≤ S → V.weight (closedBall y r) ≠ ⊤ :=
    fun y hy r hr => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono (hball y hy r hr)).trans hmass)
  have hQ : ∀ (y : Amb n ℓ) (t : ℝ), 0 < t → 0 ≤ (V.weight (closedBall y t)).toReal / t ^ n :=
    fun y t ht => div_nonneg ENNReal.toReal_nonneg (pow_pos ht n).le
  have hpow : ∀ r : ℝ, 0 < r → r ≤ R → Λ * (r / R) ^ (1 - (n : ℝ) / p) ≤ Λ :=
    fun r hr hrR => mul_le_of_le_one_right hΛ.le
      (Real.rpow_le_one (div_nonneg hr.le hR.le) ((div_le_one hR).2 hrR) hα.le)
  -- The monotonicity at `|y| ≤ 3δρ`: `ted_lp_monotonicity` at `(y, R, S, Λ)`, since `B_S(y) ⊆ U`,
  -- `∫_{B_S(y)} |H|ᵖ dμ_V < ∞` and `K(y, R) ≤ δ = κ Λ` by `aal_allard_subball_bounds`.
  have key : ∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∃ F : ℝ → ℝ,
      (∀ r : ℝ, 0 < r → r ≤ R → Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧
        |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p)) ∧
      ∀ s r : ℝ, 0 < s → s ≤ r → r ≤ R →
        F s * ((V.weight (closedBall y s)).toReal / s ^ n) + (F s - 1) ≤
          F r * ((V.weight (closedBall y r)).toReal / r ^ n) + (F r - 1) := by
    intro y hy
    obtain ⟨hSU, hSint, -, -⟩ :=
      aal_allard_subball_bounds n ℓ p hp U V H δ ρ hA y S hS hSρ (hball y hy S le_rfl)
    obtain ⟨-, -, hKR, -⟩ :=
      aal_allard_subball_bounds n ℓ p hp U V H δ ρ hA y R hR hRρ (hball y hy R hRS.le)
    obtain ⟨F, hF, hFmono⟩ := Submission.ted_lp_monotonicity n ℓ hn p hp U hU V H hHMC y R S Λ
      hR hRS hΛ hSU hSint (by rwa [hκΛ])
    exact ⟨F, fun r hr hrR => ⟨(hF r hr hrR).1, (hF r hr hrR).2.1, (hF r hr hrR).2.2.2 hΛ1⟩,
      hFmono⟩
  -- (i) Upper mass bound: `F(s) s⁻ⁿ μ(B_s(y)) = Φ(s) − (F(s) − 1) ≤ Φ(R) + Λ`.
  have upper : ∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 →
      V.weight (closedBall y s) ≤ ENNReal.ofReal ((1 + C * δ) * (unitBallVolume n * s ^ n)) := by
    intro y hy s hs hsρ
    have hsR : s ≤ R := hsρ.trans hρR
    obtain ⟨F, hF, hFmono⟩ := key y hy
    obtain ⟨hFs, -, hFs1⟩ := hF s hs hsR
    obtain ⟨-, hFR, hFR1⟩ := hF R hR le_rfl
    -- `R⁻ⁿ μ(B_R(y)) ≤ (1 + δ)(1 − 4δ)⁻ⁿ ω_n`, as `μ(B_R(y)) ≤ μ(B_ρ(0)) ≤ (1 + δ) ω_n ρⁿ`.
    have hmR : (V.weight (closedBall y R)).toReal / R ^ n ≤
        (1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n := by
      have hq : 0 < (1 - 4 * δ) ^ n := pow_pos (by linarith) n
      have hRn : R ^ n = (1 - 4 * δ) ^ n * ρ ^ n := by rw [← hRdef, mul_pow]
      rw [div_le_iff₀ (pow_pos hR n), hRn]
      calc (V.weight (closedBall y R)).toReal ≤ (1 + δ) * (unitBallVolume n * ρ ^ n) :=
            ENNReal.toReal_le_of_le_ofReal (mul_pos (by linarith) (mul_pos hω (pow_pos hρ n))).le
              ((measure_mono (hball y hy R hRS.le)).trans hmass)
        _ = (1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n * ((1 - 4 * δ) ^ n * ρ ^ n) := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hq.ne']
            ring
    have h1 : F s * ((V.weight (closedBall y s)).toReal / s ^ n) ≤
        Real.exp Λ * ((1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n) + 2 * Λ := by
      have hΦ := hFmono s R hs hsR le_rfl
      have hFRm := mul_le_mul hFR hmR (hQ y R hR) (Real.exp_pos Λ).le
      linarith [abs_le.1 (hFs1.trans (hpow s hs hsR)), abs_le.1 (hFR1.trans (hpow R hR le_rfl))]
    -- Divide by `F(s) ≥ e^{−Λ}` and use the bound `(P)` of `ted_adb_constants`.
    have h2 : (V.weight (closedBall y s)).toReal / s ^ n ≤ (1 + C * δ) * unitBallVolume n :=
      calc (V.weight (closedBall y s)).toReal / s ^ n
          = Real.exp Λ * (Real.exp (-Λ) * ((V.weight (closedBall y s)).toReal / s ^ n)) := by
            rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp Λ * (F s * ((V.weight (closedBall y s)).toReal / s ^ n)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hFs (hQ y s hs))
              (Real.exp_pos Λ).le
        _ ≤ Real.exp Λ * (Real.exp Λ * ((1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n) + 2 * Λ) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos Λ).le
        _ = Real.exp (2 * Λ) * ((1 + δ) / (1 - 4 * δ) ^ n * unitBallVolume n) +
              2 * Real.exp Λ * Λ := by
            rw [two_mul Λ, Real.exp_add]
            ring
        _ ≤ (1 + C * δ) * unitBallVolume n := hP
    rw [div_le_iff₀ (pow_pos hs n)] at h2
    rw [ENNReal.le_ofReal_iff_toReal_le (hfin y hy s (hsR.trans hRS.le))
      (mul_nonneg (by linarith) (mul_pos hω (pow_pos hs n)).le)]
    exact h2.trans_eq (by ring)
  -- (ii) Lower mass bound: `Φ ≥ ω_n` on `(0, R]`, so `F(s) s⁻ⁿ μ(B_s(y)) ≥ ω_n − Λ`.
  have lower : ∀ y ∈ V.support, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 →
      ENNReal.ofReal ((1 - C * δ) * (unitBallVolume n * s ^ n)) ≤ V.weight (closedBall y s) := by
    intro y hyV hy s hs hsρ
    have hsR : s ≤ R := hsρ.trans hρR
    obtain ⟨F, hF, hFmono⟩ := key y hy
    obtain ⟨-, hFs, hFs1⟩ := hF s hs hsR
    have hyB : y ∈ V.support ∩ ball (0 : Amb n ℓ) ρ :=
      ⟨hyV, mem_ball_zero_iff.2 (by linarith)⟩
    have hΦ : unitBallVolume n ≤
        F s * ((V.weight (closedBall y s)).toReal / s ^ n) + (F s - 1) :=
      aal_monotone_quantity_ge_density n (1 - (n : ℝ) / p) (unitBallVolume n) R Λ
        (fun u => (V.weight (closedBall y u)).toReal) F hα hω hR
        (fun u hu huR => (hF u hu huR).2.2) hFmono
        (fun ε hε => by
          filter_upwards [Submission.ted_density_ge_one n ℓ hn p hp U hU V H δ ρ hA y hyB ε hε,
            Ioo_mem_nhdsGT hR] with u hu huR
          exact (ENNReal.ofReal_le_iff_le_toReal (hfin y hy u (huR.2.le.trans hRS.le))).1 hu)
        s hs hsR
    -- Divide by `F(s) ≤ e^Λ` and use the bound `(M)` of `ted_adb_constants`.
    have h2 : (1 - C * δ) * unitBallVolume n ≤ (V.weight (closedBall y s)).toReal / s ^ n :=
      calc (1 - C * δ) * unitBallVolume n ≤ Real.exp (-Λ) * (unitBallVolume n - Λ) := hM
        _ ≤ Real.exp (-Λ) * (F s * ((V.weight (closedBall y s)).toReal / s ^ n)) :=
            mul_le_mul_of_nonneg_left
              (by linarith [abs_le.1 (hFs1.trans (hpow s hs hsR))]) (Real.exp_pos _).le
        _ ≤ Real.exp (-Λ) * (Real.exp Λ * ((V.weight (closedBall y s)).toReal / s ^ n)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hFs (hQ y s hs))
              (Real.exp_pos _).le
        _ = (V.weight (closedBall y s)).toReal / s ^ n := by
            rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [le_div_iff₀ (pow_pos hs n)] at h2
    rw [ENNReal.ofReal_le_iff_le_toReal (hfin y hy s (hsR.trans hRS.le))]
    exact (le_of_eq (by ring)).trans h2
  refine ⟨upper, lower, ?_, ?_⟩
  · -- (iii) `μ_V(B_r(x)) / (ω_n rⁿ) ≤ 1 + Cδ` on `(0, ρ/2]` by (i); it tends to `θ(x)` a.e.
    filter_upwards [(ted_tangent_plane_facts n ℓ hn U hU V).2.2.2.1] with x hx hxρ
    have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ), V.weight (closedBall x r) /
        ENNReal.ofReal (unitBallVolume n * r ^ n) ≤ ENNReal.ofReal (1 + C * δ) := by
      filter_upwards [Ioc_mem_nhdsGT (half_pos hρ)] with r hr
      refine ENNReal.div_le_of_le_mul ?_
      rw [← ENNReal.ofReal_mul (by linarith)]
      exact upper x hxρ r hr.1 hr.2
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 (le_of_tendsto hx hle)
  · -- (iv) The upper density theorem on `W = B̆_ρ(0)`, where `μ_V(W) ≤ μ_V(B_ρ(0)) < ∞`.
    exact Submission.ted_adb_support_diff_carrier_null n ℓ U V (ball 0 ρ) isOpen_ball
      ((measure_mono ball_subset_closedBall).trans_lt (hmass.trans_lt ENNReal.ofReal_lt_top))
      fun y hy => ⟨1 - 1 / 2, by norm_num,
        Submission.ted_density_ge_one n ℓ hn p hp U hU V H δ ρ hA y hy (1 / 2) (by norm_num)⟩
/-- **Affine approximation of almost-harmonic Lipschitz maps** (Simon Ch. 5, proof of
Theorem 4.5, steps (17)–(19)).  Assume the Harmonic Approximation Lemma 3.1.  For `n ≥ 1` and `ℓ`
there is `C = C(n, ℓ) > 0` such that for every `ε ∈ (0, 1)` there is `δ_ε > 0` with the following
property: if `f : ℝⁿ → ℝ^ℓ` is Lipschitz on `B_r(0)`, `|f| ≤ h` on `B̆_r(0)`,
`∫_{B̆_r} |Df|² ≤ E rⁿ` and `|∫_{B̆_r} ∇fʲ · ∇ζ| ≤ δ_ε √E sup|∇ζ| rⁿ` for all `ζ ∈ C^∞_c(B̆_r)`,
then there are `a ∈ ℝ^ℓ` and a linear `A` with `|A| ≤ C √E`, `|a| ≤ C (h + r √(εE))` and
`∫_{B̆_{er}} |f - (a + A x)|² ≤ C (ε + e^{n+4}) E r^{n+2}` for `e ∈ (0, 1/4]`.

Proof: rescale each component to `F_j(z) = fʲ(rz)/(r√E)`, apply Lemma 3.1 to get harmonic `u_j`,
and use interior estimates for harmonic functions, proved here from the mean value property
`∫ u(x + y) φ(y) dy = (∫ φ) u(x)` for a smooth radial kernel `φ` (scaling argument plus Lipschitz
integration by parts), to define `a = (r√E u_j(0))_j`, `A x = (√E ∇u_j(0) · x)_j`. -/
theorem ted_harmonic_affine_approx : HarmonicApproximationLemma → ∀ n ℓ : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δε : ℝ, 0 < δε ∧ ∀ (r E h : ℝ) (f : Rn n → Rn ℓ) (L : ℝ≥0), 0 < r → 0 < E → 0 ≤ h → LipschitzOnWith L f (closedBall 0 r) → (∀ x ∈ ball (0 : Rn n) r, ‖f x‖ ≤ h) → ∫ x in ball (0 : Rn n) r, hsNormSq (fderiv ℝ f x) ≤ E * r ^ n → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 r → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in ball (0 : Rn n) r, inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤ δε * Real.sqrt E * M * r ^ n) → ∃ (a : Rn ℓ) (A : Rn n →L[ℝ] Rn ℓ), hsNorm A ≤ C * Real.sqrt E ∧ ‖a‖ ≤ C * (h + r * Real.sqrt (ε * E)) ∧ ∀ e : ℝ, 0 < e → e ≤ 1 / 4 → ∫ x in ball (0 : Rn n) (e * r), ‖f x - (a + A x)‖ ^ 2 ≤ C * (ε + e ^ (n + 4)) * E * r ^ (n + 2) := by
  intro hHAL n ℓ hn
  -- elementary inequalities, proved once in the small initial context
  have hsq2 : ∀ X Y D : ℝ, Y ^ 2 ≤ D ^ 2 → (X + Y) ^ 2 ≤ 2 * (X ^ 2 + D ^ 2) := fun X Y D h =>
    add_sq_le.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl h) zero_le_two)
  have hKP : ∀ K P ε : ℝ, 0 ≤ K → 0 ≤ P → 0 ≤ ε → ε + K * P ≤ (1 + K) * (ε + P) :=
    fun K P ε hK hP hε => by
      calc ε + K * P ≤ ε + K * P + (P + K * ε) :=
            le_add_of_nonneg_right (add_nonneg hP (mul_nonneg hK hε))
        _ = (1 + K) * (ε + P) := by ring
  have hab : ∀ a b x y : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ x → 0 ≤ y → a * y + b * x ≤ (a + b) * (x + y) :=
    fun a b x y ha hb hx hy => by
      calc a * y + b * x ≤ a * y + b * x + (a * x + b * y) :=
            le_add_of_nonneg_right (add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy))
        _ = (a + b) * (x + y) := by ring
  -- the Hilbert–Schmidt norm is controlled by the operator norm
  have hHS : ∀ A : Rn n →L[ℝ] Rn ℓ, hsNormSq A ≤ n * ‖A‖ ^ 2 := fun A => by
    unfold hsNormSq
    calc ∑ i : Fin n, ‖A (EuclideanSpace.single i 1)‖ ^ 2 ≤ ∑ _i : Fin n, ‖A‖ ^ 2 :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _)
            ((A.le_opNorm _).trans (by rw [EuclideanSpace.norm_single, norm_one, mul_one])) 2)
      _ = n * ‖A‖ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  /- Steps 1–5 (interior estimates for harmonic functions, Simon 3.2–3.4), proved from the mean
  value property for a smooth radial kernel. -/
  obtain ⟨C₁, C₃, hC₁, hC₃, HE⟩ : ∃ C₁ C₃ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₃ ∧
      ∀ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) →
      (∀ M : ℝ, 0 ≤ M → ∫⁻ x in ball (0 : Rn n) 1, ‖u x‖ₑ ≤ ENNReal.ofReal M → |u 0| ≤ C₁ * M) ∧
      (∀ M : ℝ, 0 ≤ M → ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ≤ ENNReal.ofReal M →
        ‖gradient u 0‖ ≤ C₁ * M ∧
        ∀ z : Rn n, ‖z‖ ≤ 1/4 → |u z - u 0 - inner ℝ (gradient u 0) z| ≤ C₃ * M * ‖z‖ ^ 2) := by
    /- Step 1 (kernel).  `φ(y) = -64 τ'(1 - 32|y|²)` and its potential `Ψ(y) = τ(1 - 32|y|²)`
    (`τ` = `Real.smoothTransition`), so that `∂_v Ψ(y) = φ(y) ⟪y, v⟫`; both vanish off `B_{1/5}`. -/
    obtain ⟨φ, Ψ, Lφ, LΨ, Φ, hφc, hφ0, hφcs, hφL, hΦ, hc0, hΨL, hΨcs, hΨl, hΨ0⟩ :
        ∃ (φ Ψ : Rn n → ℝ) (Lφ LΨ : ℝ≥0) (Φ : ℝ), Continuous φ ∧
          (∀ y : Rn n, 1/5 ≤ ‖y‖ → φ y = 0) ∧ HasCompactSupport φ ∧ LipschitzWith Lφ φ ∧
          (∀ y, ‖φ y‖ ≤ Φ) ∧
          (∫ y, φ y) ≠ 0 ∧ LipschitzWith LΨ Ψ ∧ HasCompactSupport Ψ ∧
          (∀ y v : Rn n, HasLineDerivAt ℝ Ψ (φ y * inner ℝ y v) y v) ∧
          (∀ y : Rn n, 1/5 ≤ ‖y‖ → Ψ y = 0) := by
      have hτ : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
      have hτd : ∀ s, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition s) s :=
        fun s => ((hτ.differentiable (by simp)) s).hasDerivAt
      have hτ'0 : ∀ s : ℝ, s < 0 → deriv Real.smoothTransition s = 0 := fun s hs => by
        rw [(Filter.eventuallyEq_of_mem (Iio_mem_nhds hs)
          (fun z hz => Real.smoothTransition.zero_of_nonpos (le_of_lt hz))).deriv_eq]
        exact deriv_const s 0
      have hq : ∀ y : Rn n, 1/5 ≤ ‖y‖ → 1 - 32 * ‖y‖ ^ 2 < 0 := fun y hy => by nlinarith
      have hnsq : ContDiff ℝ (⊤ : ℕ∞) (fun y : Rn n => 1 - 32 * ‖y‖ ^ 2) :=
        contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))
      have hφs : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : Rn n => -64 * deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2)) :=
        contDiff_const.mul (((contDiff_infty_iff_deriv.1 hτ).2).comp hnsq)
      have hΨs : ContDiff ℝ (⊤ : ℕ∞) (fun y : Rn n => Real.smoothTransition (1 - 32 * ‖y‖ ^ 2)) :=
        hτ.comp hnsq
      have hφ0 : ∀ y : Rn n, 1/5 ≤ ‖y‖ →
          -64 * deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2) = 0 :=
        fun y hy => by rw [hτ'0 _ (hq y hy), mul_zero]
      have hΨ0 : ∀ y : Rn n, 1/5 ≤ ‖y‖ → Real.smoothTransition (1 - 32 * ‖y‖ ^ 2) = 0 :=
        fun y hy => Real.smoothTransition.zero_of_nonpos (hq y hy).le
      have hcs : ∀ g : Rn n → ℝ, (∀ y : Rn n, 1/5 ≤ ‖y‖ → g y = 0) → HasCompactSupport g :=
        fun g hg => HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) (1/5)) (fun y hy =>
          hg y (by rw [mem_closedBall, dist_zero_right, not_le] at hy; exact hy.le))
      have hφcs := hcs _ hφ0
      have hΨcs := hcs _ hΨ0
      obtain ⟨Lφ, hφL⟩ := hφs.lipschitzWith_of_hasCompactSupport hφcs (by simp)
      obtain ⟨LΨ, hΨL⟩ := hΨs.lipschitzWith_of_hasCompactSupport hΨcs (by simp)
      obtain ⟨Φ, hΦ⟩ := hφcs.exists_bound_of_continuous hφs.continuous
      refine ⟨_, _, Lφ, LΨ, Φ, hφs.continuous, hφ0, hφcs, hφL, hΦ, ?_, hΨL, hΨcs, fun y v => ?_, hΨ0⟩
      · -- `∫ φ < 0`, since `-φ ≥ 0` and `τ'(c) = 1` for some `c ∈ (0, 1)`
        obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.smoothTransition
          (deriv Real.smoothTransition) (zero_lt_one' ℝ) hτ.continuous.continuousOn
          (fun x _ => hτd x)
        simp only [Real.smoothTransition.one, Real.smoothTransition.zero, sub_zero, div_one] at hcd
        have hy1 : ‖Real.sqrt ((1 - c) / 32) • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)‖ ^ 2
            = (1 - c) / 32 := by
          rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith [hc.2])]
        have hpos : 0 < ∫ y : Rn n, -(-64 * deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2)) :=
          Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
          (μ := (volume : Measure (Rn n)))
          (x := Real.sqrt ((1 - c) / 32) • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ))
          hφs.continuous.neg hφcs.neg
          (fun y => neg_nonneg.2 (mul_nonpos_of_nonpos_of_nonneg (by norm_num)
            (Real.smoothTransition.monotone.deriv_nonneg)))
          (by
            show -(-64 * deriv Real.smoothTransition (1 - 32 * _)) ≠ 0
            rw [hy1, show (1:ℝ) - 32 * ((1 - c) / 32) = c by ring, hcd]
            norm_num)
        rw [integral_neg] at hpos
        exact (neg_pos.1 hpos).ne
      · -- the line derivative of `Ψ`
        refine HasDerivAt.congr_deriv (((hτd _).comp_hasFDerivAt y
          (((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (32:ℝ)).const_sub 1)).hasLineDerivAt
            v) ?_
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
          innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
        ring
    have hc0' : 0 < |∫ y, φ y| := abs_pos.2 hc0
    have hΦ0 : 0 ≤ Φ := (norm_nonneg _).trans (hΦ 0)
    refine ⟨|∫ y, φ y|⁻¹ * Φ, |∫ y, φ y|⁻¹ * Lφ, mul_nonneg (inv_nonneg.2 hc0'.le) hΦ0,
      mul_nonneg (inv_nonneg.2 hc0'.le) Lφ.2, fun u hu => ?_⟩
    /- Step 2: smoothness of `u`, `Δu = 0`, and a bound for `Du` on `B_{9/10}`. -/
    have hC2 : ContDiffOn ℝ 2 u (ball 0 1) := hu.contDiffOn
    have hdiff : ∀ z ∈ ball (0 : Rn n) 1, HasFDerivAt u (fderiv ℝ u z) z := fun z hz =>
      ((hC2.differentiableOn (by norm_num)) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
        |>.hasFDerivAt
    have hD1 : ContDiffOn ℝ 1 (fderiv ℝ u) (ball 0 1) :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) isOpen_ball).1 hC2).2.2
    have hD1c : ContinuousOn (fderiv ℝ u) (ball 0 1) := hD1.continuousOn
    have hD2 : ∀ z ∈ ball (0 : Rn n) 1, HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z :=
      fun z hz => ((hD1.differentiableOn one_ne_zero) z hz).differentiableAt
        (isOpen_ball.mem_nhds hz) |>.hasFDerivAt
    set b := EuclideanSpace.basisFun (Fin n) ℝ with hb
    have hlap : ∀ z ∈ ball (0 : Rn n) 1, ∑ i, fderiv ℝ (fderiv ℝ u) z (b i) (b i) = 0 := by
      intro z hz
      have h0 : Laplacian.laplacian u z = 0 := (hu z hz).2.eq_of_nhds
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u b] at h0
      simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using h0
    obtain ⟨M1, hM1⟩ : ∃ M1, ∀ z ∈ closedBall (0 : Rn n) (9/10), ‖fderiv ℝ u z‖ ≤ M1 :=
      (isCompact_closedBall 0 (9/10)).exists_bound_of_continuousOn
        (hD1c.mono (closedBall_subset_ball (by norm_num)))
    have hM1' : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 (mem_closedBall_self (by norm_num)))
    have huc : ContinuousOn u (ball 0 1) := hC2.continuousOn
    set B := closedBall (0 : Rn n) (1/5) with hB
    haveI : IsFiniteMeasure (volume.restrict B) :=
      isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
    have hφB : ∀ y ∉ B, φ y = 0 := fun y hy =>
      hφ0 y (by rw [hB, mem_closedBall, dist_zero_right, not_le] at hy; exact hy.le)
    have h910 : closedBall (0 : Rn n) (9/10) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
    have hgeo : ∀ x : Rn n, ‖x‖ < 1/2 → ∀ s : ℝ, |s| ≤ 2 → ∀ y ∈ B,
        x + s • y ∈ closedBall (0 : Rn n) (9/10) := by
      intro x hx s hs y hy
      rw [hB, mem_closedBall, dist_zero_right] at hy
      rw [mem_closedBall, dist_zero_right]
      calc ‖x + s • y‖ ≤ ‖x‖ + |s| * ‖y‖ := by
            rw [← Real.norm_eq_abs, ← norm_smul]; exact norm_add_le _ _
        _ ≤ 1/2 + 2 * (1/5) := add_le_add hx.le (mul_le_mul hs hy (norm_nonneg _) zero_le_two)
        _ = 9/10 := by norm_num
    have hpath1 : ∀ x : Rn n, ‖x‖ < 1/2 → MapsTo (fun y : Rn n => x + y) B (ball 0 1) :=
      fun x hx y hy => h910 (by have h := hgeo x hx 1 (by norm_num) y hy; rwa [one_smul] at h)
    have hsr : ∀ (L : Rn n →L[ℝ] ℝ) (w : Rn n), L w = ∑ i, inner ℝ (b i) w * L (b i) := by
      intro L w
      conv_lhs => rw [← b.sum_repr' w]
      simp only [map_sum, map_smul, smul_eq_mul]
    have hpc1 : ∀ x' : Rn n, Continuous (fun y : Rn n => x' + y) := fun x' =>
      continuous_const.add continuous_id
    /- Step 3 (mean value property): `∫ φ(y) u(x + y) dy = (∫ φ) u(x)` for `‖x‖ < 1/2`.  The
    derivative of `t ↦ ∫_B φ(y) u(x + t y) dy` is `∫_B φ(y) Du(x + t y)[y] dy`, which vanishes by
    Lipschitz integration by parts against `Ψ` (`∂_v Ψ = φ ⟪·, v⟫`) and `Δu = 0`. -/
    have hMVP : ∀ x : Rn n, ‖x‖ < 1/2 → ∫ y, φ y * u (x + y) = (∫ y, φ y) * u x := by
      intro x hx
      have hpath : ∀ s : ℝ, |s| ≤ 2 → MapsTo (fun y : Rn n => x + s • y) B (ball 0 1) :=
        fun s hs y hy => h910 (hgeo x hx s hs y hy)
      have hpc : ∀ s : ℝ, ContDiff ℝ 1 (fun y : Rn n => x + s • y) := fun s =>
        contDiff_const.add (contDiff_id.const_smul s)
      have hcF : ∀ s : ℝ, |s| ≤ 2 → ContinuousOn (fun y => φ y * u (x + s • y)) B := fun s hs =>
        hφc.continuousOn.mul (huc.comp (hpc s).continuous.continuousOn (hpath s hs))
      have hcF' : ∀ s : ℝ, |s| ≤ 2 → ContinuousOn (fun y => φ y * fderiv ℝ u (x + s • y) y) B :=
        fun s hs => hφc.continuousOn.mul ((hD1c.comp (hpc s).continuous.continuousOn
          (hpath s hs)).clm_apply continuousOn_id)
      -- the radial derivative vanishes
      have hzero : ∀ t : ℝ, |t| ≤ 2 → ∫ y in B, φ y * fderiv ℝ u (x + t • y) y = 0 := by
        intro t ht
        have hin : ∀ y : Rn n, ‖y‖ ≤ 1/4 → x + t • y ∈ ball (0 : Rn n) 1 := fun y hy => by
          rw [mem_ball, dist_zero_right]
          calc ‖x + t • y‖ ≤ ‖x‖ + |t| * ‖y‖ := by
                rw [← Real.norm_eq_abs, ← norm_smul]; exact norm_add_le _ _
            _ ≤ ‖x‖ + 2 * (1/4) := add_le_add le_rfl (mul_le_mul ht hy (norm_nonneg _) zero_le_two)
            _ < 1 := by linarith
        have hext : ∀ i : Fin n, ∃ (K : ℝ≥0) (W : Rn n → ℝ), LipschitzWith K W ∧
            EqOn (fun y => fderiv ℝ u (x + t • y) (b i)) W (closedBall 0 (1/4)) := by
          intro i
          have h2 : ContDiffOn ℝ 1 (fun y => fderiv ℝ u (x + t • y) (b i)) (closedBall 0 (1/4)) :=
            (hD1.comp (hpc t).contDiffOn (fun y hy => hin y (mem_closedBall_zero_iff.1 hy))).clm_apply
              contDiffOn_const
          obtain ⟨K, hK⟩ := h2.exists_lipschitzOnWith (by norm_num) (convex_closedBall _ _)
            (isCompact_closedBall _ _)
          obtain ⟨W, hW, hEq⟩ := hK.extend_real
          exact ⟨_, W, hW, hEq⟩
        choose K W hWL hWeq using hext
        have hibp : ∀ i, ∫ y, lineDeriv ℝ (W i) y (b i) * Ψ y =
            ∫ y, lineDeriv ℝ Ψ y (-(b i)) * W i y :=
          fun i => (hWL i).integral_lineDeriv_mul_eq hΨL hΨcs (b i)
        have hL : ∀ y, ∑ i, lineDeriv ℝ (W i) y (b i) * Ψ y = 0 := by
          intro y
          by_cases hy : ‖y‖ < 1/4
          · have hz := hin y hy.le
            have hnhd : closedBall (0 : Rn n) (1/4) ∈ 𝓝 y :=
              closedBall_mem_nhds_of_mem (mem_ball_zero_iff.2 hy)
            have hline : ∀ i, lineDeriv ℝ (W i) y (b i) =
                t * fderiv ℝ (fderiv ℝ u) (x + t • y) (b i) (b i) := by
              intro i
              have hc := ((hD2 _ hz).comp y (((hasFDerivAt_id y).const_smul t).const_add x)).clm_apply
                (hasFDerivAt_const (b i) y)
              rw [((hc.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hnhd
                (fun z hz => (hWeq i hz).symm))).hasLineDerivAt (b i)).lineDeriv]
              simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply,
                ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
            simp only [hline]
            rw [← Finset.sum_mul, ← Finset.mul_sum, hlap _ hz, mul_zero, zero_mul]
          · simp only [hΨ0 y (le_trans (by norm_num) (not_lt.1 hy)), mul_zero, Finset.sum_const_zero]
        have hR : ∀ y, ∑ i, lineDeriv ℝ Ψ y (-(b i)) * W i y = -(φ y * fderiv ℝ u (x + t • y) y) := by
          intro y
          have hl : ∀ i, lineDeriv ℝ Ψ y (-(b i)) = -(φ y * inner ℝ y (b i)) := fun i => by
            rw [(hΨl y _).lineDeriv, inner_neg_right, mul_neg]
          simp only [hl]
          by_cases hy : ‖y‖ ≤ 1/4
          · have hWy : ∀ i, W i y = fderiv ℝ u (x + t • y) (b i) := fun i =>
              (hWeq i (mem_closedBall_zero_iff.2 hy)).symm
            simp only [hWy]
            rw [hsr (fderiv ℝ u (x + t • y)) y, Finset.mul_sum, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [real_inner_comm]
            ring
          · simp only [hφ0 y (le_trans (by norm_num) (not_le.1 hy).le), zero_mul, neg_zero,
              Finset.sum_const_zero]
        have hΨi : Integrable Ψ := hΨL.continuous.integrable_of_hasCompactSupport hΨcs
        have hLi : ∀ i, Integrable (fun y => lineDeriv ℝ (W i) y (b i) * Ψ y) :=
          fun i => hΨi.mul_of_top_right ((hWL i).memLp_lineDeriv (b i))
        have hRi : ∀ i, Integrable (fun y => lineDeriv ℝ Ψ y (-(b i)) * W i y) := by
          intro i
          have hfun : (fun y => lineDeriv ℝ Ψ y (-(b i)) * W i y) =
              fun y => φ y * (inner ℝ y (-(b i)) * W i y) := by
            funext y; rw [(hΨl y _).lineDeriv, mul_assoc]
          rw [hfun]
          exact (hφc.mul ((continuous_id.inner continuous_const).mul (hWL i).continuous)
            ).integrable_of_hasCompactSupport hφcs.mul_right
        have h1 : ∫ y, ∑ i, lineDeriv ℝ (W i) y (b i) * Ψ y =
            ∫ y, ∑ i, lineDeriv ℝ Ψ y (-(b i)) * W i y := by
          rw [integral_finsetSum _ (fun i _ => hLi i), integral_finsetSum _ (fun i _ => hRi i)]
          exact Finset.sum_congr rfl (fun i _ => hibp i)
        simp only [hL, hR, integral_zero, integral_neg] at h1
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hφB y hy, zero_mul])]
        exact neg_eq_zero.1 h1.symm
      -- differentiation under the integral sign
      have hIoo : ∀ s ∈ Ioo (-2:ℝ) 2, |s| ≤ 2 := fun s hs => abs_le.2 ⟨hs.1.le, hs.2.le⟩
      have hderiv : ∀ t ∈ Ioo (-2:ℝ) 2, HasDerivAt (fun t => ∫ y in B, φ y * u (x + t • y))
          (∫ y in B, φ y * fderiv ℝ u (x + t • y) y) t := by
        intro t ht
        refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioo_mem_nhds ht.1 ht.2)
          (F := fun t y => φ y * u (x + t • y)) (F' := fun t y => φ y * fderiv ℝ u (x + t • y) y)
          (bound := fun _ => Φ * (M1 * (1/5))) ?_
          ((hcF t (hIoo t ht)).integrableOn_compact (isCompact_closedBall _ _))
          ((hcF' t (hIoo t ht)).aestronglyMeasurable measurableSet_closedBall) ?_
          (integrable_const _) ?_).2
        · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
          exact (hcF s (hIoo s hs)).aestronglyMeasurable measurableSet_closedBall
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy s hs
          rw [norm_mul]
          exact mul_le_mul (hΦ y) ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul (hM1 _ (hgeo x hx s (hIoo s hs) y hy)) (mem_closedBall_zero_iff.1 hy)
              (norm_nonneg _) hM1')) (norm_nonneg _) hΦ0
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy s hs
          exact ((hdiff _ (hpath s (hIoo s hs) hy)).comp_hasDerivAt s
            ((((hasDerivAt_id s).smul_const y).const_add x).congr_deriv (one_smul ℝ y))).const_mul
              (φ y)
      -- mean value theorem in `t`
      obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t => ∫ y in B, φ y * u (x + t • y))
        (fun t => ∫ y in B, φ y * fderiv ℝ u (x + t • y) y) (zero_lt_one' ℝ)
        (fun t ht => (hderiv t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt)
        (fun t ht => hderiv t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hcd
      rw [hzero c (abs_le.2 ⟨by linarith [hc.1], by linarith [hc.2]⟩), integral_mul_const,
        setIntegral_eq_integral_of_forall_compl_eq_zero hφB,
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hφB y hy, zero_mul])] at hcd
      exact sub_eq_zero.1 hcd.symm
    /- Step 4: differentiating the mean value identity, `(∫ φ) Du(x) = ∫ φ(y) Du(x + y) dy`. -/
    have hdMVP : ∀ x : Rn n, ‖x‖ < 1/2 →
        (∫ y, φ y) • fderiv ℝ u x = ∫ y, φ y • fderiv ℝ u (x + y) := by
      intro x hx
      have hδ : 0 < 1/2 - ‖x‖ := by linarith
      have hsm : ∀ x' ∈ ball x (1/2 - ‖x‖), ‖x'‖ < 1/2 := fun x' hx' => by
        rw [mem_ball, dist_eq_norm] at hx'
        linarith [norm_sub_norm_le x' x]
      have hcF : ∀ x' : Rn n, ‖x'‖ < 1/2 → ContinuousOn (fun y => φ y * u (x' + y)) B :=
        fun x' hx' => hφc.continuousOn.mul (huc.comp (hpc1 x').continuousOn (hpath1 x' hx'))
      have hP : HasFDerivAt (fun x' => ∫ y in B, φ y * u (x' + y))
          (∫ y in B, φ y • fderiv ℝ u (x + y)) x := by
        refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => Φ * M1)
          (F := fun x' y => φ y * u (x' + y)) (F' := fun x' y => φ y • fderiv ℝ u (x' + y))
          (ball_mem_nhds x hδ) ?_ ((hcF x hx).integrableOn_compact (isCompact_closedBall _ _)) ?_ ?_
          (integrable_const _) ?_
        · filter_upwards [ball_mem_nhds x hδ] with x' hx'
          exact (hcF x' (hsm x' hx')).aestronglyMeasurable measurableSet_closedBall
        · exact (hφc.continuousOn.smul (hD1c.comp (hpc1 x).continuousOn
            (hpath1 x hx))).aestronglyMeasurable measurableSet_closedBall
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy x' hx'
          rw [norm_smul]
          exact mul_le_mul (hΦ y) (hM1 _ (by
            have h := hgeo x' (hsm x' hx') 1 (by norm_num) y hy; rwa [one_smul] at h))
            (norm_nonneg _) hΦ0
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy x' hx'
          have h := ((hdiff _ (hpath1 x' (hsm x' hx') hy)).comp x'
            ((hasFDerivAt_id x').add_const y)).const_mul (φ y)
          rwa [ContinuousLinearMap.comp_id] at h
      have heq : (fun x' => ∫ y in B, φ y * u (x' + y)) =ᶠ[𝓝 x] fun x' => (∫ y, φ y) * u x' := by
        filter_upwards [ball_mem_nhds x hδ] with x' hx'
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hφB y hy, zero_mul])]
        exact hMVP x' (hsm x' hx')
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B)
        (f := fun y => φ y • fderiv ℝ u (x + y)) (fun y hy => by rw [hφB y hy, zero_smul])]
      exact ((hdiff x (mem_ball_zero_iff.2 (by linarith))).const_mul (∫ y, φ y)).unique
        (hP.congr_of_eventuallyEq heq.symm)
    /- Step 5: the estimates. -/
    have hgen : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (ψ : Rn n → ℝ) (K : ℝ),
        0 ≤ K → (∀ y, ‖ψ y‖ ≤ K) → (∀ y ∉ ball (0 : Rn n) 1, ψ y = 0) →
        ∀ (G : Rn n → X) (M : ℝ), 0 ≤ M → ∫⁻ x in ball (0 : Rn n) 1, ‖G x‖ₑ ≤ ENNReal.ofReal M →
        ‖∫ y, ψ y • G y‖ ≤ K * M := by
      intro X _ _ ψ K hK hψ hψ0 G M hM hGM
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : Rn n) 1)
        (fun y hy => by rw [hψ0 y hy, zero_smul])]
      refine (norm_integral_le_lintegral_norm _).trans
        (ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK hM) ?_)
      calc ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal ‖ψ y • G y‖
          ≤ ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal K * ‖G y‖ₑ := by
            refine lintegral_mono (fun y => ?_)
            rw [norm_smul, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm (G y)]
            exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hψ y)) _
        _ = ENNReal.ofReal K * ∫⁻ y in ball (0 : Rn n) 1, ‖G y‖ₑ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal K * ENNReal.ofReal M := mul_le_mul_right hGM _
        _ = ENNReal.ofReal (K * M) := (ENNReal.ofReal_mul hK).symm
    have hφ1 : ∀ y ∉ ball (0 : Rn n) 1, φ y = 0 := fun y hy =>
      hφ0 y (le_trans (by norm_num) (not_lt.1 (mt mem_ball_zero_iff.2 hy)))
    have h00 : ‖(0 : Rn n)‖ < 1/2 := by rw [norm_zero]; norm_num
    refine ⟨fun M hM huM => ?_, fun M hM huM => ?_⟩
    · -- the value at the origin
      have h1 := hMVP 0 h00
      have h2 := hgen φ Φ hΦ0 hΦ hφ1 u M hM huM
      simp only [zero_add, smul_eq_mul] at h1 h2
      rw [h1, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs] at h2
      rw [mul_assoc, le_inv_mul_iff₀ hc0']
      exact h2
    · have hgn : ∀ x, ‖gradient u x‖ₑ = ‖fderiv ℝ u x‖ₑ := fun x => by
        rw [← ofReal_norm, ← ofReal_norm]
        exact congrArg ENNReal.ofReal ((InnerProductSpace.toDual ℝ (Rn n)).symm.norm_map _)
      simp only [hgn] at huM
      have hDu0 : ‖fderiv ℝ u 0‖ ≤ |∫ y, φ y|⁻¹ * Φ * M := by
        have h1 := hdMVP 0 h00
        have h2 := hgen φ Φ hΦ0 hΦ hφ1 (fderiv ℝ u) M hM huM
        simp only [zero_add] at h1
        rw [← h1, norm_smul, Real.norm_eq_abs] at h2
        rw [mul_assoc, le_inv_mul_iff₀ hc0']
        exact h2
      have hint : ∀ z : Rn n, ‖z‖ < 1/2 → Integrable (fun w => φ (w - z) • fderiv ℝ u w) := by
        intro z hz
        have hc : ContinuousOn (fun y => φ y • fderiv ℝ u (z + y)) B :=
          hφc.continuousOn.smul (hD1c.comp (hpc1 z).continuousOn (hpath1 z hz))
        have h := (hc.integrableOn_compact (μ := volume) (isCompact_closedBall _ _)).integrable_of_forall_notMem_eq_zero
            (fun y hy => by rw [hφB y hy, zero_smul])
        simpa only [add_sub_cancel] using h.comp_sub_right z
      have hshift : ∀ z : Rn n, ∫ y, φ y • fderiv ℝ u (z + y) = ∫ w, φ (w - z) • fderiv ℝ u w := by
        intro z
        have h := integral_add_left_eq_self (μ := (volume : Measure (Rn n)))
          (fun w => φ (w - z) • fderiv ℝ u w) z
        simp only [add_sub_cancel_left] at h
        exact h
      have hLipD : ∀ z : Rn n, ‖z‖ ≤ 1/4 →
          ‖fderiv ℝ u z - fderiv ℝ u 0‖ ≤ |∫ y, φ y|⁻¹ * Lφ * M * ‖z‖ := by
        intro z hz
        have hz2 : ‖z‖ < 1/2 := by linarith
        have h1 := hdMVP z hz2
        have h0 := hdMVP 0 h00
        rw [hshift] at h1 h0
        have hdiffeq : (∫ y, φ y) • (fderiv ℝ u z - fderiv ℝ u 0) =
            ∫ w, (φ (w - z) - φ (w - 0)) • fderiv ℝ u w := by
          rw [smul_sub, h1, h0, ← integral_sub (hint z hz2) (hint 0 h00)]
          simp only [sub_smul]
        have hb := hgen (fun w => φ (w - z) - φ (w - 0)) (Lφ * ‖z‖)
          (mul_nonneg Lφ.2 (norm_nonneg _))
          (fun w => by
            have h := hφL.dist_le_mul (w - z) (w - 0)
            rwa [dist_eq_norm, dist_sub_left, dist_zero_right] at h)
          (fun w hw => by
            have hw1 : 1 ≤ ‖w‖ := not_lt.1 (mt mem_ball_zero_iff.2 hw)
            rw [hφ0 (w - z) (by linarith [norm_sub_norm_le w z]), sub_zero,
              hφ0 w (by linarith), sub_self])
          (fderiv ℝ u) M hM huM
        rw [← hdiffeq, norm_smul, Real.norm_eq_abs] at hb
        rw [show |∫ y, φ y|⁻¹ * Lφ * M * ‖z‖ = |∫ y, φ y|⁻¹ * (Lφ * ‖z‖ * M) by ring,
          le_inv_mul_iff₀ hc0']
        exact hb
      refine ⟨(InnerProductSpace.toDual ℝ (Rn n)).symm.norm_map _ ▸ hDu0, fun z hz => ?_⟩
      rw [show inner ℝ (gradient u 0) z = fderiv ℝ u 0 z from
        InnerProductSpace.toDual_symm_apply]
      have hK0 : 0 ≤ |∫ y, φ y|⁻¹ * Lφ * M := mul_nonneg (mul_nonneg (inv_nonneg.2 hc0'.le) Lφ.2) hM
      have hs : closedBall (0 : Rn n) ‖z‖ ⊆ ball 0 1 := closedBall_subset_ball (by linarith)
      have hmvt := (convex_closedBall (0 : Rn n) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun y => u y - fderiv ℝ u 0 y) (f' := fun y => fderiv ℝ u y - fderiv ℝ u 0)
        (C := |∫ y, φ y|⁻¹ * Lφ * M * ‖z‖)
        (fun y hy => ((hdiff y (hs hy)).sub (fderiv ℝ u 0).hasFDerivAt).hasFDerivWithinAt)
        (fun y hy => (hLipD y ((mem_closedBall_zero_iff.1 hy).trans hz)).trans
          (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hy) hK0))
        (mem_closedBall_self (norm_nonneg z)) (mem_closedBall_zero_iff.2 le_rfl)
      simp only [map_zero, sub_zero, Real.norm_eq_abs] at hmvt
      rw [sub_right_comm, sq, ← mul_assoc]
      exact hmvt
  /- Step 6 (Cauchy–Schwarz on `B₁`): `∫_{B₁} g ≤ (ω_n S)^{1/2}` when `∫_{B₁} g² ≤ S`. -/
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (volume (ball (0 : Rn n) 1)).toReal := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := hVdef ▸ ENNReal.toReal_nonneg
  have CS : ∀ g : Rn n → ℝ≥0∞, AEMeasurable g (volume.restrict (ball (0 : Rn n) 1)) →
      ∀ S : ℝ, 0 ≤ S → ∫⁻ x in ball (0 : Rn n) 1, g x ^ 2 ≤ ENNReal.ofReal S →
      ∫⁻ x in ball (0 : Rn n) 1, g x ≤ ENNReal.ofReal (Real.sqrt V * Real.sqrt S) := by
    intro g hg S hS hgS
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (ball (0 : Rn n) 1))
      Real.HolderConjugate.two_two hg aemeasurable_const (f := g) (g := fun _ => (1 : ℝ≥0∞))
    simp only [Pi.mul_apply, mul_one, lintegral_const, Measure.restrict_apply_univ,
      ENNReal.rpow_two, one_pow, one_mul] at h
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm (ENNReal.ofReal _)]
    gcongr
    · calc (∫⁻ x in ball (0 : Rn n) 1, g x ^ 2) ^ (1 / (2 : ℝ))
          ≤ (ENNReal.ofReal S) ^ (1 / (2 : ℝ)) := by gcongr
        _ = ENNReal.ofReal (Real.sqrt S) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hS (by norm_num), Real.sqrt_eq_rpow]
    · rw [hVdef, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
        (by norm_num), ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  /- Step 7: the constant `C` (depending on `n, ℓ` only) and `δ_ε` (from Lemma 3.1). -/
  obtain ⟨C, hCpos, hC1, hC2, hC3⟩ : ∃ C : ℝ, 0 < C ∧
      Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) ≤ C ∧ Real.sqrt ℓ * C₁ * (Real.sqrt V + V) ≤ C ∧
      2 * ℓ * (1 + C₃ ^ 2 * V ^ 2) ≤ C := by
    have h1 : 0 ≤ Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) := mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC₁ (Real.sqrt_nonneg _)))
    have h2 : 0 ≤ Real.sqrt ℓ * C₁ * (Real.sqrt V + V) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC₁) (add_nonneg (Real.sqrt_nonneg _) hV0)
    have h3 : 0 ≤ 2 * (ℓ : ℝ) * (1 + C₃ ^ 2 * V ^ 2) :=
      mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _))
        (add_nonneg zero_le_one (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    exact ⟨1 + Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) + Real.sqrt ℓ * C₁ * (Real.sqrt V + V) +
        2 * ℓ * (1 + C₃ ^ 2 * V ^ 2),
      add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg one_pos h1) h2) h3,
      ((le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right h2)).trans
        (le_add_of_nonneg_right h3),
      (le_add_of_nonneg_left (add_nonneg zero_le_one h1)).trans (le_add_of_nonneg_right h3),
      le_add_of_nonneg_left (add_nonneg (add_nonneg zero_le_one h1) h2)⟩
  refine ⟨C, hCpos, ?_⟩
  intro ε hε _hε1
  obtain ⟨δ, hδ, hHA⟩ := hHAL n hn ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r E h f L hr hE hh hLip hbound henergy halmost
  /- Step 8: for each component `j`, `F_j(z) = f(rz)_j / (r√E)` (extended from `B₁` as a
  Lipschitz function) satisfies the hypotheses of Lemma 3.1 (`W^{1,2}` with weak gradient,
  energy `≤ 1`, `δ`-almost harmonic), giving a harmonic `u_j` with `∫_{B₁}|∇u_j|² ≤ 1` and
  `∫_{B₁}|u_j - F_j|² ≤ ε`. -/
  have hcomp : ∀ j : Fin ℓ, ∃ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ^ 2 ≤ 1 ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖u x - (r * Real.sqrt E)⁻¹ * f (r • x) j‖ₑ ^ 2 ≤
        ENNReal.ofReal ε := by
    have hsE : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (r * Real.sqrt E)⁻¹ := ⟨_, rfl⟩
    have hcpos : 0 < c := hc ▸ inv_pos.2 (mul_pos hr hsE)
    have hcr : c * r = (Real.sqrt E)⁻¹ := by
      rw [hc, mul_inv, mul_right_comm, inv_mul_cancel₀ hr.ne', one_mul]
    have hsB : ∀ z ∈ closedBall (0 : Rn n) 1, r • z ∈ closedBall (0 : Rn n) r := fun z hz => by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.1 hz)
    have hsB' : ∀ z ∈ ball (0 : Rn n) 1, r • z ∈ ball (0 : Rn n) r := fun z hz => by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact mul_lt_of_lt_one_right hr (mem_ball_zero_iff.1 hz)
    have hgmeas : ∀ g : Rn n → ℝ, Measurable (gradient g) := fun g =>
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
    have hng : ∀ (g : Rn n → ℝ) (z : Rn n), ‖gradient g z‖ = ‖fderiv ℝ g z‖ := fun g z =>
      (InnerProductSpace.toDual ℝ (Rn n)).symm.norm_map _
    have hig : ∀ (g : Rn n → ℝ) (z w : Rn n), inner ℝ (gradient g z) w = fderiv ℝ g z w :=
      fun g z w => InnerProductSpace.toDual_symm_apply
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) r)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    -- `|Df|²_{HS}` is integrable on `B_r` (it is bounded by `n L²`)
    have hHSint : IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) (ball (0 : Rn n) r) := by
      have hcont : Continuous (fun A : Rn n →L[ℝ] Rn ℓ => hsNormSq A) :=
        continuous_finsetSum _ (fun i _ => (continuous_id.clm_apply continuous_const).norm.pow 2)
      refine Integrable.of_bound (hcont.measurable.comp (measurable_fderiv ℝ f)).aestronglyMeasurable
        (n * L ^ 2) ((ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall
          (fun x hx => ?_)))
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      exact (hHS _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem hx) hLip) 2) (Nat.cast_nonneg _))
    -- `f` is differentiable a.e. on `B_r` (Rademacher)
    have hfdiff : ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) r)), DifferentiableAt ℝ f x := by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [hLip.ae_differentiableWithinAt_of_mem (μ := volume)] with x hx hxB
      exact (hx (ball_subset_closedBall hxB)).differentiableAt (closedBall_mem_nhds_of_mem hxB)
    intro j
    obtain ⟨fj, hfj⟩ : ∃ g : Rn n → ℝ, g = fun y => f y j := ⟨_, rfl⟩
    have hcoord : ∀ v : Rn ℓ, |v j| ≤ ‖v‖ := fun v => by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
    -- `F z = c fʲ(r z)` is Lipschitz on the closed unit ball; `Ft` is a Lipschitz extension
    have hK0 : 0 ≤ c * L * r := mul_nonneg (mul_nonneg hcpos.le L.2) hr.le
    have hFL : LipschitzOnWith ⟨c * L * r, hK0⟩ (fun z : Rn n => c * fj (r • z)) (closedBall 0 1) := by
      refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
      have h1 := hLip.dist_le_mul _ (hsB x hx) _ (hsB y hy)
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr, dist_eq_norm] at h1
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hcpos, hfj]
      show c * |f (r • x) j - f (r • y) j| ≤ c * L * r * dist x y
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((hcoord (f (r • x) - f (r • y))).trans h1) hcpos.le
    obtain ⟨Ft, hFtL, hFtEq⟩ := hFL.extend_real
    have hFtE : ∀ z ∈ closedBall (0 : Rn n) 1, Ft z = c * fj (r • z) := fun z hz => (hFtEq hz).symm
    have hFtc : Continuous Ft := hFtL.continuous
    -- gradient of `Ft` on the open ball
    have hgFt : ∀ z ∈ ball (0 : Rn n) 1, gradient Ft z = (Real.sqrt E)⁻¹ • gradient fj (r • z) := by
      intro z hz
      have heq : Ft =ᶠ[𝓝 z] fun z => c * fj (r • z) :=
        Filter.eventuallyEq_of_mem (closedBall_mem_nhds_of_mem hz) hFtE
      have h1 : fderiv ℝ (fun z : Rn n => c * fj (r • z)) z = (c * r) • fderiv ℝ fj (r • z) := by
        rw [show (fun z : Rn n => c * fj (r • z)) = c • fun z => fj (r • z) from rfl,
          fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul, smul_smul]
      rw [gradient, gradient, heq.fderiv_eq, h1, hcr, map_smul]
    have hFtb : ∀ z ∈ ball (0 : Rn n) 1, ‖Ft z‖ ≤ c * h := fun z hz => by
      rw [hFtE z (ball_subset_closedBall hz), hfj, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hcpos]
      exact mul_le_mul_of_nonneg_left ((hcoord _).trans (hbound _ (hsB' z hz))) hcpos.le
    have hgFtb : ∀ z, ‖gradient Ft z‖ ≤ c * L * r := fun z =>
      (hng Ft z).trans_le (norm_fderiv_le_of_lipschitz ℝ hFtL)
    -- `Ft ∈ W^{1,2}(B)` with weak gradient `∇Ft` (Lipschitz integration by parts)
    have hW12 : IsW12WithGradient Ft (gradient Ft) (ball 0 1) := by
      refine ⟨MemLp.of_bound hFtc.aestronglyMeasurable (c * h)
          ((ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall hFtb)),
        MemLp.of_bound (hgmeas Ft).aestronglyMeasurable (c * L * r)
          (Filter.Eventually.of_forall hgFtb), fun ζ hζ hζcs hζsupp => ?_⟩
      obtain ⟨Lζ, hζL⟩ := hζ.lipschitzWith_of_hasCompactSupport hζcs (by simp)
      have hζd : Differentiable ℝ ζ := hζ.differentiable (by simp)
      have hζout : ∀ x ∉ ball (0 : Rn n) 1, ζ x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun h => hx (hζsupp h))
      have hdζout : ∀ x ∉ ball (0 : Rn n) 1, fderiv ℝ ζ x = 0 := fun x hx =>
        fderiv_of_notMem_tsupport ℝ (fun h => hx (hζsupp h))
      have hgζ : Continuous (gradient ζ) :=
        (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hζ.continuous_fderiv (by simp))
      have hgζcs : HasCompactSupport (gradient ζ) :=
        (hζcs.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (Rn n)).symm) (map_zero _)
      have hI1 : Integrable (fun x => Ft x • gradient ζ x) :=
        (hFtc.smul hgζ).integrable_of_hasCompactSupport hgζcs.smul_left
      have hI2 : Integrable (fun x => ζ x • gradient Ft x) :=
        (hζ.continuous.integrable_of_hasCompactSupport hζcs).smul_of_top_left
          (memLp_top_of_bound (hgmeas Ft).aestronglyMeasurable (c * L * r)
            (Filter.Eventually.of_forall hgFtb))
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          rw [gradient, hdζout x hx, map_zero, smul_zero]),
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hζout x hx, zero_smul])]
      refine ext_inner_left ℝ (fun w => ?_)
      rw [inner_neg_right, ← innerSL_apply_apply (𝕜 := ℝ), ← innerSL_apply_apply (𝕜 := ℝ),
        ← (innerSL ℝ w).integral_comp_comm hI1, ← (innerSL ℝ w).integral_comp_comm hI2]
      simp only [innerSL_apply_apply, inner_smul_right]
      have hibp := hFtL.integral_lineDeriv_mul_eq (μ := volume) hζL hζcs w
      have hA : ∀ x, lineDeriv ℝ ζ x (-w) * Ft x = -(Ft x * inner ℝ w (gradient ζ x)) := fun x => by
        rw [(hζd x).lineDeriv_eq_fderiv, map_neg, real_inner_comm, hig, neg_mul, mul_comm]
      have hB : (fun x => lineDeriv ℝ Ft x w * ζ x) =ᵐ[volume]
          fun x => ζ x * inner ℝ w (gradient Ft x) := by
        filter_upwards [hFtL.ae_differentiableAt] with x hx
        rw [hx.lineDeriv_eq_fderiv, real_inner_comm, hig, mul_comm]
      rw [integral_congr_ae hB] at hibp
      simp only [hA, integral_neg] at hibp
      rw [hibp, neg_neg]
    -- energy: `∫_{B} |∇Ft|² = E⁻¹ r⁻ⁿ ∫_{B_r} |∇fʲ|² ≤ E⁻¹ r⁻ⁿ ∫_{B_r} |Df|² ≤ 1`
    have hpt : ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) r)),
        ‖gradient fj x‖ ^ 2 ≤ hsNormSq (fderiv ℝ f x) := by
      filter_upwards [hfdiff] with x hdx
      have hh : HasFDerivAt (fun y => f y j) ((EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).comp
          (fderiv ℝ f x)) x := (EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).hasFDerivAt.comp x hdx.hasFDerivAt
      have hfd : ∀ v, fderiv ℝ fj x v = (fderiv ℝ f x v) j := fun v => by
        rw [hfj, hh.fderiv]
        rfl
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have h1 : (gradient fj x) i = fderiv ℝ fj x (EuclideanSpace.single i 1) := by
        rw [← hig, EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real]
      rw [Real.norm_eq_abs, sq_abs, h1, hfd, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcoord _) 2
    have henergyF : ∫⁻ x in ball (0 : Rn n) 1, ‖gradient Ft x‖ₑ ^ 2 ≤ 1 := by
      have hint1 : Integrable (fun x => ‖gradient Ft x‖ ^ 2) (volume.restrict (ball (0 : Rn n) 1)) :=
        Integrable.of_bound ((hgmeas Ft).norm.pow_const 2).aestronglyMeasurable ((c * L * r) ^ 2)
          (Filter.Eventually.of_forall (fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            exact pow_le_pow_left₀ (norm_nonneg _) (hgFtb x) 2))
      have heq : ∫⁻ x in ball (0 : Rn n) 1, ‖gradient Ft x‖ₑ ^ 2 =
          ENNReal.ofReal (∫ x in ball (0 : Rn n) 1, ‖gradient Ft x‖ ^ 2) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint1
          (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
        refine lintegral_congr (fun x => ?_)
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
      rw [heq, ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : ∀ x ∈ ball (0 : Rn n) 1, ‖gradient Ft x‖ ^ 2 = E⁻¹ * ‖gradient fj (r • x)‖ ^ 2 :=
        fun x hx => by
          rw [hgFt x hx, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos hsE, inv_pow,
            Real.sq_sqrt hE.le]
      rw [setIntegral_congr_fun measurableSet_ball h1, integral_const_mul,
        Measure.setIntegral_comp_smul_of_pos volume (fun x => ‖gradient fj x‖ ^ 2) _ hr,
        smul_unitBall_of_pos hr, finrank_euclideanSpace_fin, smul_eq_mul]
      have h3 := (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        hHSint hpt).trans henergy
      have hrn : 0 < r ^ n := pow_pos hr n
      calc E⁻¹ * ((r ^ n)⁻¹ * ∫ x in ball (0 : Rn n) r, ‖gradient fj x‖ ^ 2)
          ≤ E⁻¹ * ((r ^ n)⁻¹ * (E * r ^ n)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hrn.le))
              (inv_nonneg.2 hE.le)
        _ = 1 := by rw [mul_comm E, ← mul_assoc (r ^ n)⁻¹, inv_mul_cancel₀ hrn.ne', one_mul,
            inv_mul_cancel₀ hE.ne']
    -- almost harmonicity, by scaling `ζ₀ = ζ(r⁻¹ ·)`
    have halmostF : ∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball 0 1 → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) →
        |∫ x in ball (0 : Rn n) 1, inner ℝ (gradient Ft x) (gradient ζ x)| ≤ δ * M := by
      intro ζ hζ hζcs hζsupp M hM
      have hζ0s : ContDiff ℝ (⊤ : ℕ∞) (fun x => ζ (r⁻¹ • x)) := hζ.comp (contDiff_const_smul _)
      have hζ0cs : HasCompactSupport (fun x => ζ (r⁻¹ • x)) := hζcs.comp_smul (inv_ne_zero hr.ne')
      have hζ0supp : tsupport (fun x => ζ (r⁻¹ • x)) ⊆ ball 0 r := by
        rw [show (fun x => ζ (r⁻¹ • x)) = ζ ∘ (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
          from rfl, tsupport_comp_eq_preimage]
        intro x hx
        have hx' := mem_ball_zero_iff.1 (hζsupp hx)
        rw [Homeomorph.smulOfNeZero_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
          inv_mul_lt_iff₀ hr, mul_one] at hx'
        exact mem_ball_zero_iff.2 hx'
      have hgζ0 : ∀ x, gradient (fun x => ζ (r⁻¹ • x)) x = r⁻¹ • gradient ζ (r⁻¹ • x) := fun x => by
        rw [gradient, gradient, fderiv_comp_smul, map_smul]
      have hM0 : ∀ x, ‖gradient (fun x => ζ (r⁻¹ • x)) x‖ ≤ r⁻¹ * M := fun x => by
        rw [hgζ0, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
        exact mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.2 hr.le)
      have hA := halmost _ hζ0s hζ0cs hζ0supp (r⁻¹ * M) hM0 j
      rw [← hfj] at hA
      have h1 : ∀ z ∈ ball (0 : Rn n) 1, inner ℝ (gradient Ft z) (gradient ζ z) =
          ((Real.sqrt E)⁻¹ * r) * inner ℝ (gradient fj (r • z))
            (gradient (fun x => ζ (r⁻¹ • x)) (r • z)) := fun z hz => by
        rw [hgFt z hz, hgζ0, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, real_inner_smul_left,
          real_inner_smul_right, mul_assoc, ← mul_assoc r, mul_inv_cancel₀ hr.ne', one_mul]
      have hrel : ∫ x in ball (0 : Rn n) 1, inner ℝ (gradient Ft x) (gradient ζ x) =
          (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) *
            ∫ x in ball (0 : Rn n) r, inner ℝ (gradient fj x) (gradient (fun x => ζ (r⁻¹ • x)) x) := by
        rw [setIntegral_congr_fun measurableSet_ball h1, integral_const_mul,
          Measure.setIntegral_comp_smul_of_pos volume
            (fun x => inner ℝ (gradient fj x) (gradient (fun x => ζ (r⁻¹ • x)) x)) _ hr,
          smul_unitBall_of_pos hr, finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc,
          mul_comm ((Real.sqrt E)⁻¹ * r)]
      have hk0 : 0 ≤ (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) :=
        mul_nonneg (inv_nonneg.2 (pow_nonneg hr.le n)) (mul_nonneg (inv_nonneg.2 hsE.le) hr.le)
      rw [hrel, abs_mul, abs_of_nonneg hk0]
      calc (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) *
            |∫ x in ball (0 : Rn n) r, inner ℝ (gradient fj x) (gradient (fun x => ζ (r⁻¹ • x)) x)|
          ≤ (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) * (δ * Real.sqrt E * (r⁻¹ * M) * r ^ n) :=
            mul_le_mul_of_nonneg_left hA hk0
        _ = δ * M := by
            field_simp
    obtain ⟨u, hu1, hu2, hu3⟩ := hHA Ft (gradient Ft) hW12 henergyF halmostF
    refine ⟨u, hu1, hu2, le_of_eq_of_le (setLIntegral_congr_fun measurableSet_ball (fun x hx => ?_)) hu3⟩
    rw [hFtE x (ball_subset_closedBall hx), hfj, ← hc]
  /- Step 9: `a = (r√E u_j(0))_j`, `A x = (√E ∇u_j(0)·x)_j`, and the three estimates. -/
  choose u hu_harm hu_en hu_cl using hcomp
  have hsE : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (r * Real.sqrt E)⁻¹ := ⟨_, rfl⟩
  have hcpos : 0 < c := hc ▸ inv_pos.2 (mul_pos hr hsE)
  have hrc : r * Real.sqrt E * c = 1 := by rw [hc]; exact mul_inv_cancel₀ (mul_pos hr hsE).ne'
  simp only [← hc] at hu_cl
  have hsV : 0 ≤ Real.sqrt V := Real.sqrt_nonneg _
  have hfc : ∀ k : Fin ℓ, ContinuousOn (fun z : Rn n => c * f (r • z) k) (ball 0 1) := fun k =>
    continuousOn_const.mul ((EuclideanSpace.proj k : Rn ℓ →L[ℝ] ℝ).continuous.comp_continuousOn
      (hLip.continuousOn.comp (continuous_const_smul r).continuousOn (fun z hz => by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        exact mul_le_of_le_one_right hr.le (mem_ball_zero_iff.1 hz).le)))
  have hdm : ∀ k : Fin ℓ, AEStronglyMeasurable (fun z => u k z - c * f (r • z) k)
      (volume.restrict (ball (0 : Rn n) 1)) := fun k =>
    ((hu_harm k).continuousOn.sub (hfc k)).aestronglyMeasurable measurableSet_ball
  -- interior estimates for each `u k`
  have hest : ∀ k : Fin ℓ, ‖gradient (u k) 0‖ ≤ C₁ * Real.sqrt V ∧
      (∀ z : Rn n, ‖z‖ ≤ 1/4 →
        |u k z - u k 0 - inner ℝ (gradient (u k) 0) z| ≤ C₃ * Real.sqrt V * ‖z‖ ^ 2) ∧
      |u k 0| ≤ C₁ * (Real.sqrt V * Real.sqrt ε + V * (c * h)) := by
    intro k
    have hg := CS (fun x => ‖gradient (u k) x‖ₑ)
      ((InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp
        (measurable_fderiv ℝ (u k))).enorm.aemeasurable 1 zero_le_one
        (by rw [ENNReal.ofReal_one]; exact hu_en k)
    rw [Real.sqrt_one, mul_one] at hg
    have h1 := CS _ (hdm k).enorm ε hε.le (hu_cl k)
    have h2 : ∫⁻ x in ball (0 : Rn n) 1, ‖c * f (r • x) k‖ₑ ≤ ENNReal.ofReal (V * (c * h)) := by
      calc ∫⁻ x in ball (0 : Rn n) 1, ‖c * f (r • x) k‖ₑ
          ≤ ∫⁻ _ in ball (0 : Rn n) 1, ENNReal.ofReal (c * h) := by
            refine setLIntegral_mono measurable_const (fun z hz => ?_)
            rw [← ofReal_norm, norm_mul, Real.norm_eq_abs, abs_of_pos hcpos]
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hcpos.le)
            exact (PiLp.norm_apply_le (f (r • z)) k).trans (hbound _ (by
              rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
              exact mul_lt_of_lt_one_right hr (mem_ball_zero_iff.1 hz)))
        _ = ENNReal.ofReal (V * (c * h)) := by
          rw [setLIntegral_const, ← ENNReal.ofReal_toReal measure_ball_lt_top.ne, ← hVdef,
            ← ENNReal.ofReal_mul (mul_nonneg hcpos.le hh), mul_comm (c * h) V]
    have hu1 : ∫⁻ x in ball (0 : Rn n) 1, ‖u k x‖ₑ ≤
        ENNReal.ofReal (Real.sqrt V * Real.sqrt ε + V * (c * h)) := by
      rw [ENNReal.ofReal_add (mul_nonneg hsV (Real.sqrt_nonneg _))
        (mul_nonneg hV0 (mul_nonneg hcpos.le hh))]
      refine le_trans (lintegral_mono (fun x => ?_))
        ((lintegral_add_left' (hdm k).enorm _).trans_le (add_le_add h1 h2))
      calc ‖u k x‖ₑ = ‖(u k x - c * f (r • x) k) + c * f (r • x) k‖ₑ := by rw [sub_add_cancel]
        _ ≤ _ := enorm_add_le _ _
    obtain ⟨hg0, hT⟩ := (HE (u k) (hu_harm k)).2 _ hsV hg
    exact ⟨hg0, hT, (HE (u k) (hu_harm k)).1 _
      (add_nonneg (mul_nonneg hsV (Real.sqrt_nonneg _)) (mul_nonneg hV0 (mul_nonneg hcpos.le hh)))
      hu1⟩
  -- the affine map
  obtain ⟨a, ha⟩ : ∃ a : Rn ℓ, a = WithLp.toLp 2 (fun k => r * Real.sqrt E * u k 0) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Rn n →L[ℝ] Rn ℓ, A = ∑ k : Fin ℓ,
      (Real.sqrt E • innerSL ℝ (gradient (u k) 0)).smulRight (EuclideanSpace.single k (1:ℝ)) :=
    ⟨_, rfl⟩
  have haapply : ∀ k, a k = r * Real.sqrt E * u k 0 := fun k => by rw [ha]
  have hAapply : ∀ (x : Rn n) (k : Fin ℓ), (A x) k = Real.sqrt E * inner ℝ (gradient (u k) 0) x :=
    fun x k => by
      rw [hA]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.smul_apply, innerSL_apply_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
        Pi.smul_apply, EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨a, A, ?_, ?_, ?_⟩
  · -- `|A| ≤ C √E`
    have hAn : ‖A‖ ≤ ℓ * (C₁ * Real.sqrt V) * Real.sqrt E := by
      rw [hA]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k : Fin ℓ, ‖(Real.sqrt E • innerSL ℝ (gradient (u k) 0)).smulRight
            (EuclideanSpace.single k (1:ℝ))‖
          ≤ ∑ _k : Fin ℓ, (C₁ * Real.sqrt V) * Real.sqrt E := Finset.sum_le_sum (fun k _ => by
            rw [ContinuousLinearMap.norm_smulRight_apply, EuclideanSpace.norm_single, norm_one,
              mul_one, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_of_pos hsE, mul_comm]
            exact mul_le_mul_of_nonneg_right (hest k).1 hsE.le)
        _ = ℓ * (C₁ * Real.sqrt V) * Real.sqrt E := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
    have h0 : 0 ≤ ℓ * (C₁ * Real.sqrt V) * Real.sqrt E :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC₁ hsV)) hsE.le
    calc hsNorm A ≤ Real.sqrt (n * (ℓ * (C₁ * Real.sqrt V) * Real.sqrt E) ^ 2) :=
          Real.sqrt_le_sqrt ((hHS A).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) hAn 2) (Nat.cast_nonneg _)))
      _ = Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) * Real.sqrt E := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq h0, ← mul_assoc]
      _ ≤ C * Real.sqrt E := mul_le_mul_of_nonneg_right hC1 hsE.le
  · -- `|a| ≤ C (h + r √(εE))`
    have hB0 : 0 ≤ C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h) :=
      mul_nonneg hC₁ (add_nonneg (mul_nonneg hsV (mul_nonneg hr.le (Real.sqrt_nonneg _)))
        (mul_nonneg hV0 hh))
    have hak : ∀ k, |a k| ≤ C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h) := fun k => by
      rw [haapply, abs_mul, abs_of_pos (mul_pos hr hsE), Real.sqrt_mul hε.le]
      calc r * Real.sqrt E * |u k 0| ≤ r * Real.sqrt E *
            (C₁ * (Real.sqrt V * Real.sqrt ε + V * (c * h))) :=
            mul_le_mul_of_nonneg_left (hest k).2.2 (mul_pos hr hsE).le
        _ = C₁ * (Real.sqrt V * (r * (Real.sqrt ε * Real.sqrt E)) +
            V * h * (r * Real.sqrt E * c)) := by ring
        _ = _ := by rw [hrc, mul_one]
    calc ‖a‖ = Real.sqrt (∑ k : Fin ℓ, ‖a k‖ ^ 2) := EuclideanSpace.norm_eq a
      _ ≤ Real.sqrt (∑ _k : Fin ℓ, (C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h)) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum (fun k _ => by
            rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hak k) 2))
      _ = Real.sqrt ℓ * (C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB0]
      _ ≤ Real.sqrt ℓ * C₁ * (Real.sqrt V + V) * (h + r * Real.sqrt (ε * E)) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hab _ _ _ _ hsV hV0 hh
            (mul_nonneg hr.le (Real.sqrt_nonneg _))) hC₁) (Real.sqrt_nonneg _)
      _ ≤ C * (h + r * Real.sqrt (ε * E)) :=
          mul_le_mul_of_nonneg_right hC2 (add_nonneg hh (mul_nonneg hr.le (Real.sqrt_nonneg _)))
  · -- the `L²` estimate
    intro e he he4
    have he1 : e ≤ 1 := he4.trans (by norm_num)
    have hrn : 0 < r ^ n := pow_pos hr n
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) e)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have hcv : ∫ x in ball (0 : Rn n) (e * r), ‖f x - (a + A x)‖ ^ 2 =
        r ^ n * ∫ z in ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2 := by
      have h := Measure.setIntegral_comp_smul_of_pos volume (fun x => ‖f x - (a + A x)‖ ^ 2)
        (ball (0 : Rn n) e) hr
      rw [smul_ball hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_comm r e,
        finrank_euclideanSpace_fin, smul_eq_mul] at h
      rw [h, ← mul_assoc, mul_inv_cancel₀ hrn.ne', one_mul]
    rw [hcv]
    -- integrability and size of `(u_k - F_k)²`
    have hsq : ∀ k, IntegrableOn (fun z => (u k z - c * f (r • z) k) ^ 2) (ball (0 : Rn n) 1) ∧
        ∫ z in ball (0 : Rn n) e, (u k z - c * f (r • z) k) ^ 2 ≤ ε := by
      intro k
      have hfi : ∫⁻ z in ball (0 : Rn n) 1, ‖(u k z - c * f (r • z) k) ^ 2‖ₑ =
          ∫⁻ z in ball (0 : Rn n) 1, ‖u k z - c * f (r • z) k‖ₑ ^ 2 :=
        lintegral_congr (fun z => enorm_pow _ _)
      have hi : IntegrableOn (fun z => (u k z - c * f (r • z) k) ^ 2) (ball (0 : Rn n) 1) :=
        ⟨(hdm k).pow 2, by rw [HasFiniteIntegral, hfi]; exact (hu_cl k).trans_lt ENNReal.ofReal_lt_top⟩
      refine ⟨hi, (setIntegral_mono_set hi (Filter.Eventually.of_forall (fun z => sq_nonneg _))
        (Filter.Eventually.of_forall (ball_subset_ball he1))).trans ?_⟩
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z => sq_nonneg _))
        ((hdm k).pow 2)]
      refine ENNReal.toReal_le_of_le_ofReal hε.le (le_trans (le_of_eq ?_) (hu_cl k))
      refine lintegral_congr (fun z => ?_)
      rw [← enorm_pow, Real.enorm_eq_ofReal (sq_nonneg _)]
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = C₃ * Real.sqrt V * e ^ 2 := ⟨_, rfl⟩
    have hD0 : 0 ≤ D := hD ▸ mul_nonneg (mul_nonneg hC₃ hsV) (sq_nonneg e)
    -- pointwise bound on `B_e`
    have hpt : ∀ z ∈ ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2 ≤
        2 * (r ^ 2 * E) * ∑ k : Fin ℓ, ((u k z - c * f (r • z) k) ^ 2 + D ^ 2) := by
      intro z hz
      have hz' : ‖z‖ ≤ 1/4 := (mem_ball_zero_iff.1 hz).le.trans he4
      rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hcomp : (f (r • z) - (a + A (r • z))) k = r * Real.sqrt E *
          (-(u k z - c * f (r • z) k) + (u k z - u k 0 - inner ℝ (gradient (u k) 0) z)) := by
        rw [WithLp.ofLp_sub, WithLp.ofLp_add, Pi.sub_apply, Pi.add_apply, haapply, hAapply,
          real_inner_smul_right]
        linear_combination (-(f (r • z) k)) * hrc
      have hY : (u k z - u k 0 - inner ℝ (gradient (u k) 0) z) ^ 2 ≤ D ^ 2 := by
        rw [← sq_abs, hD]
        exact pow_le_pow_left₀ (abs_nonneg _) (((hest k).2.1 z hz').trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z)
            (mem_ball_zero_iff.1 hz).le 2) (mul_nonneg hC₃ hsV))) 2
      rw [Real.norm_eq_abs, sq_abs, hcomp, mul_pow, mul_pow, Real.sq_sqrt hE.le]
      calc r ^ 2 * E * (-(u k z - c * f (r • z) k) + (u k z - u k 0 -
            inner ℝ (gradient (u k) 0) z)) ^ 2
          ≤ r ^ 2 * E * (2 * ((-(u k z - c * f (r • z) k)) ^ 2 + D ^ 2)) :=
            mul_le_mul_of_nonneg_left (hsq2 _ _ _ hY) (mul_nonneg (sq_nonneg r) hE.le)
        _ = 2 * (r ^ 2 * E) * ((u k z - c * f (r • z) k) ^ 2 + D ^ 2) := by ring
    have hint : ∀ k, IntegrableOn (fun z => (u k z - c * f (r • z) k) ^ 2 + D ^ 2)
        (ball (0 : Rn n) e) := fun k =>
      ((hsq k).1.mono_set (ball_subset_ball he1)).add (integrable_const _)
    have hvol : ∫ _ in ball (0 : Rn n) e, D ^ 2 = e ^ n * V * D ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Measure.addHaar_ball_of_pos volume _ he,
        finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg he.le n),
        ← hVdef]
    have hP : e ^ n * V * D ^ 2 = C₃ ^ 2 * V ^ 2 * (e ^ n * e ^ 4) := by
      rw [hD, mul_pow, mul_pow, Real.sq_sqrt hV0]; ring
    have h2rE : 0 ≤ 2 * (r ^ 2 * E) := mul_nonneg zero_le_two (mul_nonneg (sq_nonneg r) hE.le)
    calc r ^ n * ∫ z in ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2
        ≤ r ^ n * ∫ z in ball (0 : Rn n) e, 2 * (r ^ 2 * E) * ∑ k : Fin ℓ,
          ((u k z - c * f (r • z) k) ^ 2 + D ^ 2) :=
          mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => sq_nonneg _))
            ((integrable_finsetSum _ (fun k _ => hint k)).const_mul _)
            ((ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall hpt))) hrn.le
      _ = r ^ n * (2 * (r ^ 2 * E) * ∑ k : Fin ℓ,
          ((∫ z in ball (0 : Rn n) e, (u k z - c * f (r • z) k) ^ 2) + e ^ n * V * D ^ 2)) := by
          rw [integral_const_mul, integral_finsetSum _ (fun k _ => hint k)]
          congr 2
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [integral_add ((hsq k).1.mono_set (ball_subset_ball he1)) (integrable_const _), hvol]
      _ ≤ r ^ n * (2 * (r ^ 2 * E) * ∑ _k : Fin ℓ, (ε + e ^ n * V * D ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum
            (fun k _ => add_le_add (hsq k).2 le_rfl)) h2rE) hrn.le
      _ ≤ r ^ n * (2 * (r ^ 2 * E) * ∑ _k : Fin ℓ,
          ((1 + C₃ ^ 2 * V ^ 2) * (ε + e ^ n * e ^ 4))) := by
          rw [hP]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum
            (fun k _ => hKP _ _ _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
              (mul_nonneg (pow_nonneg he.le n) (pow_nonneg he.le 4)) hε.le)) h2rE) hrn.le
      _ = (2 * ℓ * (1 + C₃ ^ 2 * V ^ 2)) * (ε + e ^ (n + 4)) * E * r ^ (n + 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_add,
            pow_add]
          ring
      _ ≤ C * (ε + e ^ (n + 4)) * E * r ^ (n + 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3
            (add_nonneg hε.le (pow_nonneg he.le _))) hE.le) (pow_nonneg hr.le _)
/-- **Area Jacobian of a linear graph** (Simon Ch. 5, proof of Theorem 4.5, p. 119:
`1 ≤ J_F ≤ 1 + C |∇f|²`).  For `D : ℝⁿ →L ℝ^ℓ` with Gram matrix `G = (⟨D eₐ, D e_b⟩)_{a,b}`, the
area Jacobian of `v ↦ (v, D v)` is `J(D) = √det(I + G)`; then `1 ≤ J(D)`, and `‖D‖ ≤ 1` implies
`J(D) ≤ 1 + (e^{n/2}/2) |D|²`.  `G` is symmetric positive semidefinite with `trace G = |D|²`, so
`1 ≤ det(I + G) ≤ exp |D|²` and `1 ≤ J(D) ≤ exp(|D|²/2)`.  If `‖D‖ ≤ 1` then `0 ≤ |D|² ≤ n ‖D‖² ≤ n`,
and `exp(s/2) ≤ 1 + (e^{T/2}/2) s` for `0 ≤ s ≤ T` (with `s = |D|²`, `T = n`). -/
theorem gwe_graph_jacobian_bounds : ∀ (n ℓ : ℕ) (D : Rn n →L[ℝ] Rn ℓ), 1 ≤ Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ))))) ∧ (‖D‖ ≤ 1 → Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ))))) ≤ 1 + Real.exp ((n : ℝ) / 2) / 2 * hsNormSq D) := by
  intro n ℓ D
  -- Steps 1, 2, 6: the Gram matrix `G` of `D` is symmetric positive semidefinite, `trace G = |D|²`.
  obtain ⟨hsymm, hpsd, htr⟩ := Submission.gwe_gjb_gram_symm_psd_trace n ℓ D
  -- Steps 3, 4, 7: `1 ≤ det(I + G) ≤ exp (trace G) = exp |D|²`.
  obtain ⟨hdet, hdet_le⟩ := Submission.gwe_gjb_det_one_add_bounds n _ hsymm hpsd
  rw [htr] at hdet_le
  refine ⟨?_, fun hD => ?_⟩
  · -- Step 5: `J(D) = √det(I + G) ≥ √1 = 1`.
    exact Real.one_le_sqrt.2 hdet
  · -- Step 9: `0 ≤ |D|² ≤ n ‖D‖² ≤ n`, since `‖D‖ ≤ 1`.
    obtain ⟨h0, hle, -⟩ := (Submission.lgc_hsNormSq_bounds n ℓ).2 D
    have hn : hsNormSq D ≤ n :=
      hle.trans (mul_le_of_le_one_right (Nat.cast_nonneg n) (pow_le_one₀ (norm_nonneg D) hD))
    -- Steps 8, 10, 11: `J(D) ≤ √(exp |D|²) = exp (|D|²/2) ≤ 1 + (e^{n/2}/2) |D|²`.
    calc Real.sqrt _ ≤ Real.sqrt (Real.exp (hsNormSq D)) := Real.sqrt_le_sqrt hdet_le
      _ = Real.exp (hsNormSq D / 2) := (Real.exp_half _).symm
      _ ≤ 1 + Real.exp ((n : ℝ) / 2) / 2 * hsNormSq D := Submission.gwe_gjb_exp_half_le _ _ h0 hn
/-- The linear algebra of Simon Ch. 5, proof of Theorem 4.5, displays (7), (10), (11) and (13)
(pp. 118–119). For a linear isometry `q` of `ℝ^{n+ℓ}` and a linear map `D : ℝⁿ → ℝ^ℓ` with
`‖D‖ ≤ 1`, let `p` be the orthogonal projection onto the rotated graph plane
`S = span{q(v, Dv) : v ∈ ℝⁿ}` and `P` the one onto `T = q(ℝⁿ × {0})`. Then
(a) `|D|² ≤ (ℓ + ½)|p − P|²`, and (b) `|⟨p e'_j, p q(w, 0)⟩ − ⟨r, w⟩| ≤ |p − P|² |w|` whenever `r`
is the `j`-th row of `D`, where `e'_j = q(0, ε_j)`.
The horizontal vectors `q(a, 0)` lie in `T`, with `|q(a, 0)| = |a|` and
`⟨q(a, 0), q(b, 0)⟩ = ⟨a, b⟩`. By (7), `p e'_j = p q(r, 0)`, so the projection defect (10)–(11)
on `T` bounds the error in (b) by `|p − P|² |r| |w|`, and `|r| ≤ ‖D‖ ≤ 1`. For (a), the same
bound with `u = w = q(r_j, 0)` gives `|r_j|² ≤ |p e'_j|² + |p − P|²`. Summing over `j` and using
`|D|² = Σ_j |r_j|²` and the trace identity `Σ_j |p e'_j|² = ½|p − P|²` (13), valid because
`dim S = n`, gives (a). -/
theorem gwe_graph_tilt_algebra : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (D : Rn n →L[ℝ] Rn ℓ), ‖D‖ ≤ 1 → hsNormSq D ≤ ((ℓ : ℝ) + 1 / 2) * hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection - (rotatedPlane q).starProjection) ∧ ∀ (j : Fin ℓ) (r w : Rn n), (∀ v : Rn n, inner ℝ r v = D v j) → |inner ℝ ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))) ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint w 0))) - inner ℝ r w| ≤ hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection - (rotatedPlane q).starProjection) * ‖w‖ := by
  intro n ℓ q D hD
  -- (L4) and (IP) for graph points, and (L5) `P(q(a, b)) = q(a, 0)`
  obtain ⟨-, -, -, -, -, hnorm, hinner⟩ := Submission.any_radius_gr_la_graphPoint_algebra n ℓ
  obtain ⟨hproj, -, -⟩ := Submission.any_radius_gr_la_rotatedPlane_facts n ℓ q
  -- the horizontal vectors `q(a, 0)` lie in `T`, have norm `|a|` and inner products `⟨a, b⟩`
  have hmem : ∀ a : Rn n, q (graphPoint a 0) ∈ rotatedPlane q := fun a =>
    Submodule.starProjection_eq_self_iff.mp (hproj a 0)
  have hnorm0 : ∀ a : Rn n, ‖q (graphPoint a 0)‖ = ‖a‖ := fun a => by
    have h := hnorm a 0
    rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
    rw [LinearIsometryEquiv.norm_map]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  have hinner0 : ∀ a b : Rn n,
      inner ℝ (q (graphPoint a 0)) (q (graphPoint b 0)) = inner ℝ a b := fun a b => by
    rw [LinearIsometryEquiv.inner_map_map, hinner, inner_zero_left, add_zero]
  -- the rows `R j` of `D`; Simon (7); the trace identity (13) for `S`, of dimension `n`; and the
  -- projection defect (10)–(11) for `S` and `T`
  obtain ⟨hrow, R, hR, hRsum⟩ := Submission.gwe_gta_row_bounds n ℓ D
  have horth := Submission.gwe_gta_graph_row_orthogonal n ℓ q D
  have hvert := Submission.gwe_gta_vertical_trace_sum n ℓ q _
    (Submission.tdo_gpd_graph_plane_finrank n ℓ q D)
  have hdefect := Submission.gwe_gta_proj_inner_defect (n + ℓ)
    (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))) (rotatedPlane q)
  generalize Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v))) = S
    at horth hvert hdefect ⊢
  have hE : 0 ≤ hsNormSq (S.starProjection - (rotatedPlane q).starProjection) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  generalize hsNormSq (S.starProjection - (rotatedPlane q).starProjection) = E
    at hvert hdefect hE ⊢
  refine ⟨?_, ?_⟩
  -- (a): `|R j|² ≤ |p e'_j|² + E` for every row, and `Σ_j |p e'_j|² = E / 2`
  · have hj : ∀ j : Fin ℓ, ‖R j‖ ^ 2 ≤
        ‖S.starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ ^ 2 + E := by
      intro j
      have h := hdefect _ _ (hmem (R j)) (hmem (R j))
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← horth j (R j) (hR j),
        hnorm0] at h
      have h1 : ‖R j‖ ≤ 1 := (hrow j (R j) (hR j)).trans hD
      have h2 : E * (‖R j‖ * ‖R j‖) ≤ E :=
        mul_le_of_le_one_right hE ((mul_le_of_le_one_left (norm_nonneg _) h1).trans h1)
      linarith [(abs_le.mp h).1]
    calc hsNormSq D = ∑ j : Fin ℓ, ‖R j‖ ^ 2 := hRsum.symm
      _ ≤ ∑ j : Fin ℓ,
            (‖S.starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ ^ 2 + E) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = E / 2 + ℓ * E := by
          rw [Finset.sum_add_distrib, hvert, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
      _ = ((ℓ : ℝ) + 1 / 2) * E := by ring
  -- (b): by (7), `p e'_j = p q(r, 0)`; then the projection defect and `|r| ≤ ‖D‖ ≤ 1`
  · intro j r w hr
    rw [horth j r hr]
    have h := hdefect _ _ (hmem r) (hmem w)
    rw [hinner0, hnorm0, hnorm0] at h
    have h1 : ‖r‖ ≤ 1 := (hrow j r hr).trans hD
    exact h.trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg w) h1) hE)

/-- Simon Ch. 2, 3.5 (area formula) for a rotated Lipschitz graph, as used in the proof of Ch. 5,
Theorem 4.5: if `f` is `K`-Lipschitz on `B_R(0)`, `A ⊆ B_R(0)` is Borel and `q` is a linear isometry
of `ℝ^{n+ℓ}`, then `∫_{q(graph f|A)} g dHⁿ = ∫_A J_f(x) g(q(x, f(x))) dx` for every `g ≥ 0`, where
`J_f = √det(I + (Df eₐ · Df e_b)_{a,b})`. Extend `f` to a globally Lipschitz `f'`; the graph map
`G x = q(x, f' x)` is injective, Lipschitz and does not decrease distances. For linear `D`, the map
`T_D v = q(v, D v)` is an isometry after an endomorphism `W` of `ℝⁿ` with `|det W| = J(D)`, so
`Hⁿ(T_D(s)) = J(D) Lⁿ(s)` (Simon (3.1)) and `J(D) ≥ 1`. Split a set of differentiability points
of `f'` into the cells `tᵐ ≤ J(Df') < tᵐ⁺¹` and these into pieces on which `G` is `δ`-close to
some `T_{Df'(y)}`: there `Hⁿ(G(·))` and `∫ J(Df')` agree up to `t²`. Letting `t → 1` and using
Rademacher, `Hⁿ(G(·)) = J(Df') Lⁿ`, which transfers to integrals along the embedding `G`.
Finally `f = f'` near almost every point of `A`, as the sphere `∂B_R(0)` is null. -/
theorem gwe_lipschitz_graph_area_formula : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (K : ℝ≥0) (R : ℝ), LipschitzOnWith K f (closedBall 0 R) → ∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ g : Amb n ℓ → ℝ≥0∞, ∫⁻ y in q '' graphOver f A, g y ∂(μHE[n] : Measure (Amb n ℓ)) = ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ)))))) * g (q (graphPoint x (f x))) := by
  intro n ℓ hn q f K R hf A hA hAR g
  -- graph coordinates: `(a, b) - (a', b') = (a - a', b - b')`, `|(a, b)|² = |a|² + |b|²`
  obtain ⟨hsub, hnorm, -, -⟩ := lip_approx_graph_coordinates n ℓ q
  -- `⟨(a, b), (a', b')⟩ = ⟨a, a'⟩ + ⟨b, b'⟩`
  have hinner : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      inner ℝ (graphPoint a b) (graphPoint a' b') = inner ℝ a a' + inner ℝ b b' := by
    intro a a' b b'
    simp only [graphPoint, PiLp.inner_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  -- `(a, b) ↦ graphPoint a b` is the linear isomorphism `ℝⁿ × ℝ^ℓ ≃ ℝ^{n+ℓ}`
  let Φ := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := ℓ)).symm
  have hgp : ∀ (a : Rn n) (b : Rn ℓ), graphPoint a b = Φ (a, b) := by
    intro a b
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp [Φ, graphPoint]
    · simp [Φ, graphPoint]
  -- the Jacobian `J(D) = √det(I + (⟨D eₐ, D e_b⟩))` of the graph of a linear map `D`
  obtain ⟨J, hJ⟩ : ∃ J : (Rn n →L[ℝ] Rn ℓ) → ℝ, ∀ D, J D = Real.sqrt (Matrix.det
      ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
        inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ))))) :=
    ⟨_, fun _ => rfl⟩
  have hJcont : Continuous J := by
    rw [show J = _ from funext hJ]
    fun_prop
  -- the graph map `T D : v ↦ q(v, D v)` of a linear map `D`
  obtain ⟨T, hT⟩ : ∃ T : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Amb n ℓ),
      ∀ D v, T D v = q (graphPoint v (D v)) :=
    ⟨fun D => (q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ) ∘L
      ((Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ) ∘L ((ContinuousLinearMap.id ℝ (Rn n)).prod D)),
      fun D v => by simp [hgp]⟩
  have hTinner : ∀ D u w, inner ℝ (T D u) (T D w) = inner ℝ u w + inner ℝ (D u) (D w) := by
    intro D u w
    rw [hT, hT, LinearIsometryEquiv.inner_map_map, hinner]
  have hTnorm : ∀ D v, ‖v‖ ≤ ‖T D v‖ := by
    intro D v
    have h := hTinner D v v
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [sq_nonneg ‖D v‖])
  have hTinj : ∀ D, Function.Injective (T D) := by
    intro D x y hxy
    have h := hTnorm D (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  -- Simon (3.1), linear area formula: `Hⁿ(T D (s)) = J(D) Lⁿ(s)`
  have hlin : ∀ D (s : Set (Rn n)),
      (μHE[n] : Measure (Amb n ℓ)) (T D '' s) = ENNReal.ofReal (J D) * volume s := by
    intro D s
    have hTinj' : Function.Injective (T D : Rn n →ₗ[ℝ] Amb n ℓ) := hTinj D
    set V : Submodule ℝ (Amb n ℓ) := LinearMap.range (T D : Rn n →ₗ[ℝ] Amb n ℓ) with hVdef
    have hV : Module.finrank ℝ V = n := by
      rw [hVdef, LinearMap.finrank_range_of_inj hTinj', finrank_euclideanSpace_fin]
    set bV : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hV)
    -- `T D = ι ∘ W` with `ι` a linear isometry and `W` an endomorphism of `ℝⁿ`
    set W : Rn n →ₗ[ℝ] Rn n := (bV.repr.toLinearEquiv : V →ₗ[ℝ] Rn n) ∘ₗ
      (T D : Rn n →ₗ[ℝ] Amb n ℓ).rangeRestrict
    set ι : Rn n →ₗᵢ[ℝ] Amb n ℓ := V.subtypeₗᵢ.comp bV.repr.symm.toLinearIsometry
    have hιW : ∀ v, ι (W v) = T D v := by
      intro v
      simp [ι, W]
    have himage : T D '' s = ι '' (W '' s) := by
      rw [Set.image_image]
      exact Set.image_congr fun v _ => (hιW v).symm
    rw [himage, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap]
    congr 2
    -- `|det W| = √det(Wᵀ W)` and `Wᵀ W = I + (⟨D eₐ, D e_b⟩)`
    set M := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis W with hM
    have hWinner : ∀ u w, inner ℝ (W u) (W w) = inner ℝ (T D u) (T D w) := by
      intro u w
      rw [← hιW, ← hιW, LinearIsometry.inner_map_map]
    have hgram : (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of (fun a b : Fin n =>
        inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) =
        M.transpose * M := by
      ext a b
      have h1 := hWinner (EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single b (1 : ℝ))
      rw [hTinner, EuclideanSpace.inner_single_left, PiLp.inner_apply] at h1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply,
        Matrix.transpose_apply, hM, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_toBasis,
        PiLp.basisFun_apply, PiLp.basisFun_repr]
      simp only [map_one, one_mul, PiLp.ofLp_single, Pi.single_apply, RCLike.inner_apply,
        conj_trivial] at h1
      rw [Finset.sum_congr rfl (fun x _ => mul_comm _ _), h1]
    rw [hJ, hgram, Matrix.det_mul, Matrix.det_transpose, hM, LinearMap.det_toMatrix, ← sq,
      Real.sqrt_sq_eq_abs]
  -- comparison of image measures through a pairwise distance bound
  have hcomp : ∀ (φ ψ : Rn n → Amb n ℓ) (s : Set (Rn n)) (c : ℝ≥0), Set.InjOn ψ s →
      (∀ x ∈ s, ∀ y ∈ s, dist (φ x) (φ y) ≤ c * dist (ψ x) (ψ y)) →
      (μHE[n] : Measure (Amb n ℓ)) (φ '' s) ≤ (c : ℝ≥0∞) ^ n * μHE[n] (ψ '' s) := by
    intro φ ψ s c hψ hd
    have hh : LipschitzOnWith c (φ ∘ Function.invFunOn ψ s) (ψ '' s) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [Function.comp_apply, hψ.leftInvOn_invFunOn hx, hψ.leftInvOn_invFunOn hy]
        using hd x hx y hy
    have himage : (φ ∘ Function.invFunOn ψ s) '' (ψ '' s) = φ '' s := by
      rw [Set.image_comp, hψ.invFunOn_image Set.Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hh
  -- `J(D) ≥ 1`: `T D` does not decrease distances
  have hJ1 : ∀ D, 1 ≤ J D := by
    intro D
    have hiso : Isometry (fun v : Rn n => q (graphPoint v 0)) := by
      refine Isometry.of_dist_eq fun x y => ?_
      have h := hnorm (x - y) 0
      rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, hsub, sub_zero]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
    have hB := hcomp (fun v => q (graphPoint v 0)) (T D) (closedBall 0 1) 1 (hTinj D).injOn
      (fun x _ y _ => by
        rw [hiso.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
        exact hTnorm D (x - y))
    rw [hiso.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      hlin, ENNReal.coe_one, one_pow, one_mul] at hB
    have hpos : volume (closedBall (0 : Rn n) 1) ≠ 0 :=
      (measure_closedBall_pos volume 0 one_pos).ne'
    have hfin : volume (closedBall (0 : Rn n) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
    exact ENNReal.one_le_ofReal.mp
      ((ENNReal.mul_le_mul_iff_left hpos hfin).mp (by rwa [one_mul]))
  -- Step 1: extend `f` from `B_R(0)` to a globally Lipschitz map `f'`
  obtain ⟨f', hf'L, hf'eq⟩ := hf.extend_finite_dimension
  -- Step 2: the graph map `G x = q(x, f' x)` is Lipschitz, injective, and expands distances
  obtain ⟨G, hG⟩ : ∃ G : Rn n → Amb n ℓ, ∀ x, G x = q (graphPoint x (f' x)) :=
    ⟨_, fun _ => rfl⟩
  have hGL : LipschitzWith (1 * (‖(Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ)‖₊ *
      max 1 (lipschitzExtensionConstant (Rn ℓ) * K))) G := by
    have h := q.lipschitzWith.comp ((Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ).lipschitzWith.comp
      (LipschitzWith.id.prodMk hf'L))
    convert h using 1
    funext x
    simp [hG, hgp]
  have hGdist : ∀ x y, dist x y ≤ dist (G x) (G y) := by
    intro x y
    have h := hnorm (x - y) (f' x - f' y)
    rw [dist_eq_norm, dist_eq_norm, hG, hG, ← map_sub, LinearIsometryEquiv.norm_map, hsub]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by rw [h]; nlinarith [sq_nonneg ‖f' x - f' y‖])
  have hGinj : Function.Injective G := by
    intro x y hxy
    have h := hGdist x y
    rw [hxy, dist_self] at h
    exact dist_le_zero.mp h
  have hGemb : MeasurableEmbedding G := hGL.continuous.measurableEmbedding hGinj
  -- at a differentiability point of `f'`, `DG(x) v = q(v, Df'(x) v)`
  have hGd : ∀ x, DifferentiableAt ℝ f' x → HasFDerivAt G (T (fderiv ℝ f' x)) x := by
    intro x hdx
    have h1 : HasFDerivAt (fun y => (y, f' y))
        ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ f' x)) x :=
      (hasFDerivAt_id x).prodMk hdx.hasFDerivAt
    have h2 := (Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ).hasFDerivAt.comp x h1
    have h3 := (q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).hasFDerivAt.comp x h2
    convert h3 using 1
    · funext y
      simp [hG, hgp]
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [hT, hgp]
  -- Step 3: the measures `ν(s) = Hⁿ(G(s))` and `ρ = J(Df') Lⁿ` on `ℝⁿ`
  set ν : Measure (Rn n) := Measure.comap G (μHE[n] : Measure (Amb n ℓ)) with hνdef
  have hν : ∀ s, ν s = (μHE[n] : Measure (Amb n ℓ)) (G '' s) := fun s =>
    hGemb.comap_apply _ s
  have hJm : Measurable fun x => J (fderiv ℝ f' x) :=
    hJcont.measurable.comp (measurable_fderiv ℝ f')
  have hjmeas : Measurable fun x => ENNReal.ofReal (J (fderiv ℝ f' x)) :=
    ENNReal.measurable_ofReal.comp hJm
  set ρ : Measure (Rn n) := (volume : Measure (Rn n)).withDensity
    (fun x => ENNReal.ofReal (J (fderiv ℝ f' x))) with hρdef
  have hρ : ∀ s, MeasurableSet s →
      ρ s = ∫⁻ x in s, ENNReal.ofReal (J (fderiv ℝ f' x)) := fun s hs =>
    withDensity_apply _ hs
  -- countable additivity transfers a ratio bound from a partition to its union
  have hsum : ∀ (μ₁ μ₂ : Measure (Rn n)) (c : ℝ≥0∞) (B : Set (Rn n)) (P : ℕ → Set (Rn n)),
      (∀ k, MeasurableSet (P k)) → Pairwise (Function.onFun Disjoint P) → B = ⋃ k, P k →
      (∀ k, μ₁ (P k) ≤ c * μ₂ (P k)) → μ₁ B ≤ c * μ₂ B := by
    intro μ₁ μ₂ c B P hPm hPd hB hle
    rw [hB, measure_iUnion hPd hPm, measure_iUnion hPd hPm, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hle
  -- Step 4: `ν ≤ t² ρ` and `ρ ≤ t² ν` on measurable sets of differentiability points, `t > 1`
  have hDmeas : MeasurableSet {x : Rn n | DifferentiableAt ℝ f' x} :=
    measurableSet_of_differentiableAt ℝ f'
  have hpiece : ∀ t : ℝ≥0, 1 < t → ∀ B, MeasurableSet B →
      B ⊆ {x : Rn n | DifferentiableAt ℝ f' x} →
      ν B ≤ (t : ℝ≥0∞) ^ 2 * ρ B ∧ ρ B ≤ (t : ℝ≥0∞) ^ 2 * ν B := by
    intro t ht B hB hBD
    have ht' : (1 : ℝ) < t := by exact_mod_cast ht
    -- an approximation error `δ` with `(1 + δ)ⁿ ≤ t` and `(1 - δ)⁻ⁿ ≤ t`
    obtain ⟨δ, hδpos, hδ1, hδup, hδlow⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ δ < 1 ∧ (1 + δ) ^ n < t ∧
        ((1 - δ)⁻¹) ^ n < t := by
      have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ < 1 := eventually_lt_nhds zero_lt_one
      have hupper : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (1 + δ) ^ n < t :=
        ((continuousAt_const.add continuousAt_id).pow _).eventually_lt continuousAt_const
          (by simpa using ht)
      have hlower : ∀ᶠ δ : ℝ≥0 in 𝓝 0, ((1 - δ)⁻¹) ^ n < t := by
        apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using ht)
        apply ContinuousAt.pow
        apply ContinuousAt.inv₀
        · exact continuousAt_const.sub continuousAt_id
        · simp
      have hevent : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, 0 < δ ∧ δ < 1 ∧ (1 + δ) ^ n < t ∧
          ((1 - δ)⁻¹) ^ n < t := by
        filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
          hupper.filter_mono nhdsWithin_le_nhds, hlower.filter_mono nhdsWithin_le_nhds]
          with δ h1 h2 h3 h4
        exact ⟨h1, h2, h3, h4⟩
      exact hevent.exists
    have hup : ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n ≤ t := by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδup.le
    have hlow : (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n ≤ t := by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδlow.le
    have hpow : ∀ m : ℕ, ENNReal.ofReal ((t : ℝ) ^ m) = (t : ℝ≥0∞) ^ m := by
      intro m
      rw [ENNReal.ofReal_pow (NNReal.coe_nonneg t), ENNReal.ofReal_coe_nnreal]
    -- the cells `C m = {x ∈ B : tᵐ ≤ J(Df'(x)) < tᵐ⁺¹}` (recall `J ≥ 1`)
    obtain ⟨C, hC⟩ : ∃ C : ℕ → Set (Rn n), ∀ m, C m = B ∩ {x | (t : ℝ) ^ m ≤ J (fderiv ℝ f' x) ∧
        J (fderiv ℝ f' x) < (t : ℝ) ^ (m + 1)} := ⟨_, fun _ => rfl⟩
    have hCmeas : ∀ m, MeasurableSet (C m) := fun m => by
      rw [hC]
      exact hB.inter ((measurableSet_le measurable_const hJm).inter
        (measurableSet_lt hJm measurable_const))
    have hCdisj : Pairwise (Function.onFun Disjoint C) := by
      intro m m' hmm'
      rw [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      rw [hC] at hx hx'
      have e1 : m < m' + 1 := (pow_lt_pow_iff_right₀ ht').mp (hx.2.1.trans_lt hx'.2.2)
      have e2 : m' < m + 1 := (pow_lt_pow_iff_right₀ ht').mp (hx'.2.1.trans_lt hx.2.2)
      exact hmm' (by omega)
    have hCcover : B = ⋃ m, C m := by
      ext x
      simp only [mem_iUnion, hC, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hx
        obtain ⟨m, hm⟩ := exists_nat_pow_near (hJ1 (fderiv ℝ f' x)) ht'
        exact ⟨m, hx, hm⟩
      · rintro ⟨m, hx, -⟩
        exact hx
    have hcell : ∀ m, ν (C m) ≤ (t : ℝ≥0∞) ^ 2 * ρ (C m) ∧
        ρ (C m) ≤ (t : ℝ≥0∞) ^ 2 * ν (C m) := by
      intro m
      rcases (C m).eq_empty_or_nonempty with hempty | hne
      · simp [hempty]
      have hCD : C m ⊆ {x : Rn n | DifferentiableAt ℝ f' x} := fun x hx => by
        rw [hC] at hx
        exact hBD hx.1
      -- pieces of `C m` on which `G` is `δ`-close to `T(Df'(y))` for some `y ∈ C m`
      obtain ⟨P, L, hPdisj, hPmeas, hPcover, hPapprox, hPL⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G (C m)
          (fun x => T (fderiv ℝ f' x))
          (fun x hx => (hGd x (hCD hx)).hasFDerivWithinAt) (fun _ => δ) (fun _ => hδpos.ne')
      have hQmeas : ∀ k, MeasurableSet (C m ∩ P k) := fun k => (hCmeas m).inter (hPmeas k)
      have hQdisj : Pairwise (Function.onFun Disjoint fun k => C m ∩ P k) := fun i j hij =>
        (hPdisj hij).mono inter_subset_right inter_subset_right
      have hQcover : C m = ⋃ k, C m ∩ P k := by
        rw [← inter_iUnion]
        exact (inter_eq_left.2 hPcover).symm
      have hpc : ∀ k, ν (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ 2 * ρ (C m ∩ P k) ∧
          ρ (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ 2 * ν (C m ∩ P k) := by
        intro k
        obtain ⟨y, hy, hLy⟩ := hPL hne k
        have hQ : ApproximatesLinearOn G (T (fderiv ℝ f' y)) (C m ∩ P k) δ := by
          have h := hPapprox k
          rwa [hLy] at h
        rw [hC] at hy
        have hJy1 : (t : ℝ≥0∞) ^ m ≤ ENNReal.ofReal (J (fderiv ℝ f' y)) := by
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hy.2.1
        have hJy2 : ENNReal.ofReal (J (fderiv ℝ f' y)) ≤ (t : ℝ≥0∞) ^ (m + 1) := by
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hy.2.2.le
        have hρlow : (t : ℝ≥0∞) ^ m * volume (C m ∩ P k) ≤ ρ (C m ∩ P k) := by
          rw [hρ _ (hQmeas k), ← setLIntegral_const]
          refine setLIntegral_mono hjmeas fun x hx => ?_
          have hx1 := hx.1
          rw [hC] at hx1
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hx1.2.1
        have hρup : ρ (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ (m + 1) * volume (C m ∩ P k) := by
          rw [hρ _ (hQmeas k), ← setLIntegral_const]
          refine setLIntegral_mono measurable_const fun x hx => ?_
          have hx1 := hx.1
          rw [hC] at hx1
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hx1.2.2.le
        -- `G` and `T(Df'(y))` have comparable distances on the piece
        have hd1 : ∀ x ∈ C m ∩ P k, ∀ z ∈ C m ∩ P k, dist (G x) (G z) ≤
            ((1 + δ : ℝ≥0) : ℝ) * dist (T (fderiv ℝ f' y) x) (T (fderiv ℝ f' y) z) := by
          intro x hx z hz
          have happ := hQ x hx z hz
          have hl := hTnorm (fderiv ℝ f' y) (x - z)
          rw [map_sub] at happ hl
          rw [dist_eq_norm, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
          calc ‖G x - G z‖ ≤ ‖G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z)‖ +
                ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := norm_le_norm_sub_add _ _
            _ ≤ δ * ‖x - z‖ + ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by gcongr
            _ ≤ δ * ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ +
                ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by gcongr
            _ = (1 + δ) * ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by ring
        have hd2 : ∀ x ∈ C m ∩ P k, ∀ z ∈ C m ∩ P k,
            dist (T (fderiv ℝ f' y) x) (T (fderiv ℝ f' y) z) ≤
              (((1 - δ)⁻¹ : ℝ≥0) : ℝ) * dist (G x) (G z) := by
          intro x hx z hz
          have happ : ‖G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z)‖ ≤
              δ * ‖x - z‖ := by
            simpa only [map_sub] using hQ x hx z hz
          have hl : ‖x - z‖ ≤ ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by
            simpa only [map_sub] using hTnorm (fderiv ℝ f' y) (x - z)
          have hδR : (δ : ℝ) < 1 := by exact_mod_cast hδ1
          have htri : ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ ≤ ‖G x - G z‖ +
              ‖G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z)‖ := by
            have h := norm_sub_le (G x - G z)
              (G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z))
            rwa [sub_sub_cancel] at h
          have hm := mul_le_mul_of_nonneg_left hl (NNReal.coe_nonneg δ)
          have key : ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ ≤ ‖G x - G z‖ +
              δ * ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by linarith
          rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ1.le, NNReal.coe_one,
            inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hδR), mul_sub, mul_one, mul_comm]
          linarith
        constructor
        · calc ν (C m ∩ P k) = μHE[n] (G '' (C m ∩ P k)) := hν _
            _ ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] (T (fderiv ℝ f' y) '' (C m ∩ P k)) :=
              hcomp G _ _ _ (hTinj _).injOn hd1
            _ = ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n *
                (ENNReal.ofReal (J (fderiv ℝ f' y)) * volume (C m ∩ P k)) := by
              rw [hlin]
            _ ≤ (t : ℝ≥0∞) * ((t : ℝ≥0∞) ^ (m + 1) * volume (C m ∩ P k)) := by gcongr
            _ = (t : ℝ≥0∞) ^ 2 * ((t : ℝ≥0∞) ^ m * volume (C m ∩ P k)) := by ring
            _ ≤ (t : ℝ≥0∞) ^ 2 * ρ (C m ∩ P k) := by gcongr
        · calc ρ (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ (m + 1) * volume (C m ∩ P k) := hρup
            _ = (t : ℝ≥0∞) * ((t : ℝ≥0∞) ^ m * volume (C m ∩ P k)) := by ring
            _ ≤ (t : ℝ≥0∞) * (ENNReal.ofReal (J (fderiv ℝ f' y)) * volume (C m ∩ P k)) := by
              gcongr
            _ = (t : ℝ≥0∞) * μHE[n] (T (fderiv ℝ f' y) '' (C m ∩ P k)) := by rw [hlin]
            _ ≤ (t : ℝ≥0∞) * ((((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] (G '' (C m ∩ P k))) := by
              gcongr
              exact hcomp _ G _ _ hGinj.injOn hd2
            _ ≤ (t : ℝ≥0∞) * ((t : ℝ≥0∞) * ν (C m ∩ P k)) := by
              rw [hν]
              gcongr
            _ = (t : ℝ≥0∞) ^ 2 * ν (C m ∩ P k) := by ring
      exact ⟨hsum ν ρ _ (C m) _ hQmeas hQdisj hQcover fun k => (hpc k).1,
        hsum ρ ν _ (C m) _ hQmeas hQdisj hQcover fun k => (hpc k).2⟩
    exact ⟨hsum ν ρ _ B C hCmeas hCdisj hCcover fun m => (hcell m).1,
      hsum ρ ν _ B C hCmeas hCdisj hCcover fun m => (hcell m).2⟩
  -- Step 5: letting `t → 1`, `ν = ρ` on sets of differentiability points
  have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
    intro a
    have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
      (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
    simpa only [one_pow, one_mul] using
      ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
  have hD : ∀ B, MeasurableSet B → B ⊆ {x : Rn n | DifferentiableAt ℝ f' x} → ν B = ρ B := by
    intro B hB hBD
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hpiece t ht B hB hBD).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hpiece t ht B hB hBD).2
  -- Step 6: `ν = ρ`, as both vanish on the null set of nondifferentiability points (Rademacher)
  have hDnull : volume {x : Rn n | ¬ DifferentiableAt ℝ f' x} = 0 :=
    ae_iff.mp hf'L.ae_differentiableAt
  have hmain : ν = ρ := by
    ext B hB
    have h1 : ν (B \ {x : Rn n | DifferentiableAt ℝ f' x}) = 0 := by
      rw [hν]
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hGL.lipschitzOnWith (s := B \ {x : Rn n | DifferentiableAt ℝ f' x}))
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
        measure_mono_null (fun x hx => hx.2) hDnull, mul_zero] at h
      exact le_zero_iff.mp h
    have h2 : ρ (B \ {x : Rn n | DifferentiableAt ℝ f' x}) = 0 :=
      withDensity_absolutelyContinuous _ _ (measure_mono_null (fun x hx => hx.2) hDnull)
    rw [← measure_inter_add_sdiff B hDmeas, ← measure_inter_add_sdiff (μ := ρ) B hDmeas, h1, h2,
      hD _ (hB.inter hDmeas) inter_subset_right]
  -- Step 7: transfer the integral along the measurable embedding `G`
  have himg : q '' graphOver f A = G '' A := by
    rw [graphOver, Set.image_image]
    refine Set.image_congr fun x hx => ?_
    rw [hG, hf'eq (hAR hx)]
  have hGA : MeasurableSet (G '' A) := hGemb.measurableSet_image' hA
  have hpres : MeasurePreserving G ν ((μHE[n] : Measure (Amb n ℓ)).restrict (range G)) :=
    ⟨hGemb.measurable, hGemb.map_comap _⟩
  calc ∫⁻ y in q '' graphOver f A, g y ∂(μHE[n] : Measure (Amb n ℓ))
      = ∫⁻ y in G '' A, g y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (range G)) := by
        rw [himg, Measure.restrict_restrict hGA, inter_eq_left.2 (image_subset_range G A)]
    _ = ∫⁻ x in A, g (G x) ∂ν := (hpres.setLIntegral_comp_emb hGemb g A).symm
    _ = ∫⁻ x in A, g (G x) ∂ρ := by rw [hmain]
    _ = ∫⁻ x in A, ENNReal.ofReal (J (fderiv ℝ f' x)) * g (G x) := by
        rw [hρdef, restrict_withDensity hA,
          lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hjmeas.aemeasurable
            (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        rfl
    _ = _ := by
        -- a.e. on `A`, `x` is interior to `B_R(0)`, where `f = f'`
        refine setLIntegral_congr_fun_ae hA ?_
        have hnt : Nontrivial (Rn n) := by
          have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
          infer_instance
        have hsph : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∉ sphere (0 : Rn n) R :=
          measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume 0 R)
        filter_upwards [hsph] with x hxs hxA
        have hxb : x ∈ ball (0 : Rn n) R := by
          have h1 := hAR hxA
          rw [mem_closedBall] at h1
          rw [mem_sphere] at hxs
          exact mem_ball.mpr (lt_of_le_of_ne h1 hxs)
        have hev : f =ᶠ[𝓝 x] f' :=
          Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hxb) fun y hy =>
            hf'eq (ball_subset_closedBall hy)
        rw [hJ, hG, hev.fderiv_eq, hf'eq (hAR hxA)]
/-- **Pull-back of the varifold weight to the parameter domain of a 1-Lipschitz graph** (the
transfer step "from (12), (13) and the area formula" in the proof of Simon Ch. 5, 4.5).  With
`F(x) = q(x, f(x))`, `J = J_f` and `B = B_R(0)`, the weight `μ_V` restricted to `F(A)` has the Borel
density `W = J · g₂ ∘ F̂` over Borel `A ⊆ B`, where `g₂ ≥ 0` is a Borel version of `1_M θ`
(`gwe_vgt_weight_density`) and `F̂` a Borel version of `F` (`gwe_vgt_graph_measurability`).

Proof: `J ≥ 1` (`gwe_graph_jacobian_bounds`), so the area formula
(`gwe_lipschitz_graph_area_formula`, `K = 1`, `g = 1`) gives `Lⁿ(B') ≤ Hⁿ(F(B'))` for Borel
`B' ⊆ B`; hence `F` pulls `Hⁿ`-null sets back to `Lⁿ`-null subsets of `B`, and
`g₂(F̂ x) = 1_M θ (F x)` for a.e. `x ∈ B`, which is (c).  For (a),
`∫_{F(A)} φ dμ_V = ∫_{F(A)} 1_M θ φ dHⁿ = ∫_A J (1_M θ ∘ F) (φ ∘ F) dLⁿ` and the a.e. identity.
(b) and (d) follow from (a) with `F̂ = F` on `A` (`gwe_vgt_transfer_consequences`, `G = F̂`). -/
theorem gwe_varifold_graph_transfer : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ), LipschitzOnWith 1 f (closedBall 0 R) → ∃ W : Rn n → ℝ, Measurable W ∧ (∀ x, 0 ≤ W x) ∧ (∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ φ : Amb n ℓ → ℝ≥0∞, ∫⁻ y in q '' graphOver f A, φ y ∂V.weight = ∫⁻ x in A, ENNReal.ofReal (W x) * φ (q (graphPoint x (f x)))) ∧ (∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ φ : Amb n ℓ → ℝ, Measurable φ → ∫ y in q '' graphOver f A, φ y ∂V.weight = ∫ x in A, W x * φ (q (graphPoint x (f x)))) ∧ (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 R → W x = Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ))))) * V.carrier.indicator V.mult (q (graphPoint x (f x)))) ∧ ∀ Z : Set (Amb n ℓ), V.weight Z = 0 → ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ closedBall 0 R → q (graphPoint x (f x)) ∈ Z → W x = 0 := by
  intro n ℓ hn U V q f R hf
  -- The graph Jacobian `J = J_f`; `J ≥ 1` by JB (i) with `D = Df(x)`.
  obtain ⟨J, hJ⟩ : ∃ J : Rn n → ℝ, ∀ x, Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ))))) = J x :=
    ⟨_, fun _ => rfl⟩
  have hJ1 : ∀ x, 1 ≤ J x := fun x => by
    rw [← hJ x]
    exact (Submission.gwe_graph_jacobian_bounds n ℓ (fderiv ℝ f x)).1
  have hJ0 : ∀ x, 0 ≤ J x := fun x => zero_le_one.trans (hJ1 x)
  -- (P2)-(P4): `F(A)` is Borel, `F̂` is a Borel version of `F` on `B`, and `J` is Borel.
  obtain ⟨hFA, ⟨Fh, hFh, hFhF⟩, hJm⟩ :=
    Submission.gwe_vgt_graph_measurability n ℓ q f R hf.continuousOn
  simp only [hJ] at hJm
  -- AREA with `K = 1`.
  have harea := Submission.gwe_lipschitz_graph_area_formula n ℓ hn q f 1 R hf
  simp only [hJ] at harea
  -- (P5): `Lⁿ(B') ≤ Hⁿ(F(B'))` for Borel `B' ⊆ B`.
  have hP5 : ∀ B' : Set (Rn n), MeasurableSet B' → B' ⊆ closedBall 0 R →
      volume B' ≤ (μHE[n] : Measure (Amb n ℓ)) (q '' graphOver f B') := by
    intro B' hB' hB'R
    calc volume B' = ∫⁻ _ in B', 1 := (setLIntegral_one B').symm
      _ ≤ ∫⁻ x in B', ENNReal.ofReal (J x) * 1 := setLIntegral_mono' hB' fun x _ => by
          rw [mul_one]
          exact ENNReal.one_le_ofReal.2 (hJ1 x)
      _ = ∫⁻ _ in q '' graphOver f B', 1 ∂(μHE[n] : Measure (Amb n ℓ)) :=
          (harea B' hB' hB'R fun _ => 1).symm
      _ = (μHE[n] : Measure (Amb n ℓ)) (q '' graphOver f B') := setLIntegral_one _
  -- (P6): `F` pulls `Hⁿ`-null sets back to `Lⁿ`-null subsets of `B`.
  have hP6 : ∀ Y : Set (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) Y = 0 →
      ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ closedBall 0 R → q (graphPoint x (f x)) ∉ Y := by
    intro Y hY
    obtain ⟨Y', hYY', hY'm, hY'0⟩ := exists_measurable_superset_of_null hY
    have hB'm : MeasurableSet (closedBall (0 : Rn n) R ∩ Fh ⁻¹' Y') :=
      measurableSet_closedBall.inter (hFh hY'm)
    have hB'0 : volume (closedBall (0 : Rn n) R ∩ Fh ⁻¹' Y') = 0 := by
      refine le_antisymm ?_ zero_le
      calc volume (closedBall (0 : Rn n) R ∩ Fh ⁻¹' Y')
          ≤ (μHE[n] : Measure (Amb n ℓ)) (q '' graphOver f (closedBall 0 R ∩ Fh ⁻¹' Y')) :=
            hP5 _ hB'm inter_subset_left
        _ ≤ (μHE[n] : Measure (Amb n ℓ)) Y' := by
            refine measure_mono ?_
            rintro _ ⟨_, ⟨x, ⟨hxB, hxY'⟩, rfl⟩, rfl⟩
            rw [mem_preimage, hFhF x hxB] at hxY'
            exact hxY'
        _ = 0 := hY'0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hB'0] with x hx hxB hxY
    exact hx ⟨hxB, by rw [mem_preimage, hFhF x hxB]; exact hYY' hxY⟩
  -- Step 1: a Borel version `g₂ ≥ 0` of `1_M θ`, and (*) `g₂ ∘ F̂ = 1_M θ ∘ F` a.e. on `B`.
  obtain ⟨⟨g₂, hg₂m, hg₂0, hg₂⟩, hdens⟩ := Submission.gwe_vgt_weight_density n ℓ U V
  have hstar : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ closedBall 0 R →
      g₂ (Fh x) = V.carrier.indicator V.mult (q (graphPoint x (f x))) := by
    filter_upwards [hP6 _ (ae_iff.1 hg₂)] with x hx hxB
    rw [hFhF x hxB]
    by_contra h
    exact hx hxB h
  -- Step 2: `W = J · g₂ ∘ F̂`.
  have hWm : Measurable fun x => J x * g₂ (Fh x) := hJm.mul (hg₂m.comp hFh)
  have hW0 : ∀ x, 0 ≤ J x * g₂ (Fh x) := fun x => mul_nonneg (hJ0 x) (hg₂0 _)
  -- (a): the density of `μ_V`, AREA applied to `1_M θ φ`, and (*).
  have ha : ∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ φ : Amb n ℓ → ℝ≥0∞,
      ∫⁻ y in q '' graphOver f A, φ y ∂V.weight =
        ∫⁻ x in A, ENNReal.ofReal (J x * g₂ (Fh x)) * φ (q (graphPoint x (f x))) := by
    intro A hA hAR φ
    rw [hdens _ (hFA A hA hAR) φ, harea A hA hAR]
    refine setLIntegral_congr_fun_ae hA ?_
    filter_upwards [hstar] with x hx hxA
    rw [hx (hAR hxA), ENNReal.ofReal_mul (hJ0 x), mul_assoc]
  -- (b) and (d): `gwe_vgt_transfer_consequences` with `G = F̂`, which equals `F` on `A ⊆ B`.
  have htr := fun (A : Set (Rn n)) (hA : MeasurableSet A) (hAR : A ⊆ closedBall 0 R) =>
    Submission.gwe_vgt_transfer_consequences n ℓ V.weight (q '' graphOver f A) A Fh
      (fun x => J x * g₂ (Fh x)) hA hFh hWm hW0 fun φ _ => by
        rw [ha A hA hAR φ]
        exact setLIntegral_congr_fun hA fun x hx => by simp only [hFhF x (hAR hx)]
  refine ⟨fun x => J x * g₂ (Fh x), hWm, hW0, ha, ?_, ?_, ?_⟩
  · intro A hA hAR φ hφ
    rw [(htr A hA hAR).1 φ hφ]
    exact setIntegral_congr_fun hA fun x hx => by simp only [hFhF x (hAR hx)]
  · filter_upwards [hstar] with x hx hxR
    show J x * g₂ (Fh x) = _
    rw [hJ x, hx (ball_subset_closedBall hxR)]
  · intro Z hZ
    filter_upwards [(htr (closedBall 0 R) measurableSet_closedBall subset_rfl).2 Z hZ]
      with x hx hxB hxZ
    exact hx hxB (by rw [hFhF x hxB]; exact hxZ)
/-- Simon Ch. 5, proof of Theorem 4.5, step 1(v): a `C¹` function with `tsupport ζ ⊆ B̆_r(0)` and
`|∇ζ| ≤ M` satisfies `|ζ| ≤ M r`. For `|y| < r` pick a unit vector `w` with `|y − r w| ≤ r`
(`w = y/|y|`, or a standard basis vector if `y = 0`, which needs `n ≥ 1`); then `ζ(r w) = 0` and
the mean value inequality (`Convex.norm_image_sub_le_of_norm_fderiv_le`, with
`‖Dζ‖ = ‖∇ζ‖` since the Riesz map is an isometry) gives `|ζ(y)| ≤ M |y − r w| ≤ M r`. -/
theorem gwe_vfv_abs_le_grad_bound_mul_radius : ∀ n : ℕ, 1 ≤ n → ∀ (ζ : Rn n → ℝ) (r M : ℝ), 0 ≤ r → Differentiable ℝ ζ → tsupport ζ ⊆ ball 0 r → (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ y, |ζ y| ≤ M * r := by
  intro n hn ζ r M hr hζ hsupp hM y
  -- `M ≥ ‖∇ζ(0)‖ ≥ 0`
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- `ζ` vanishes off `B̆_r(0)`
  have hzero : ∀ z : Rn n, r ≤ ‖z‖ → ζ z = 0 := by
    intro z hz
    by_contra h
    have hz' := hsupp (subset_tsupport ζ h)
    rw [mem_ball_zero_iff] at hz'
    linarith
  -- `‖Dζ(x)‖ = ‖∇ζ(x)‖ ≤ M`, the Riesz map being a linear isometry equivalence
  have hD : ∀ x, ‖fderiv ℝ ζ x‖ ≤ M := by
    intro x
    have h := hM x
    rwa [gradient, LinearIsometryEquiv.norm_map] at h
  rcases le_or_gt r ‖y‖ with hy | hy
  · rw [hzero y hy, abs_zero]
    exact mul_nonneg hM0 hr
  -- a unit vector `w` with `‖y − r w‖ ≤ r`
  obtain ⟨w, hw1, hw2⟩ : ∃ w : Rn n, ‖w‖ = 1 ∧ ‖y - r • w‖ ≤ r := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · refine ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp, ?_⟩
      rw [hy0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      simp
    · have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      refine ⟨‖y‖⁻¹ • y, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy'.ne']
      · have hyw : y - r • (‖y‖⁻¹ • y) = (1 - r * ‖y‖⁻¹) • y := by
          rw [smul_smul, sub_smul, one_smul]
        have hc : 1 - r * ‖y‖⁻¹ ≤ 0 := by
          rw [sub_nonpos, ← div_eq_mul_inv, le_div_iff₀ hy', one_mul]
          exact hy.le
        rw [hyw, norm_smul, Real.norm_eq_abs, abs_of_nonpos hc, neg_sub, sub_mul, mul_assoc,
          inv_mul_cancel₀ hy'.ne', mul_one, one_mul]
        linarith
  -- `ζ(r w) = 0`, and the mean value inequality on `ℝⁿ`
  have hrw : ζ (r • w) = 0 :=
    hzero _ (by rw [norm_smul, hw1, Real.norm_eq_abs, abs_of_nonneg hr, mul_one])
  have hmv : ‖ζ y - ζ (r • w)‖ ≤ M * ‖y - r • w‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hζ x) (fun x _ => hD x)
      (mem_univ _) (mem_univ _)
  calc |ζ y| = ‖ζ y - ζ (r • w)‖ := by rw [hrw, sub_zero, Real.norm_eq_abs]
    _ ≤ M * ‖y - r • w‖ := hmv
    _ ≤ M * r := mul_le_mul_of_nonneg_left hw2 hM0

/-- Simon Ch. 5, proof of Theorem 4.5, display (5) (p. 117): `x` is no farther from the origin
than its coordinate along `T = q(ℝⁿ × {0})` plus its height over `T`. For a linear isometry `q` of
`ℝ^{n+ℓ}`, `|x| ≤ |a(x)| + dist(x, T)`, where `a(x) ∈ ℝⁿ` is the first block of `q⁻¹ x`.
Writing `q⁻¹ x = (a, b)`, `p_{T⊥} x = q(a, b) − q(a, 0) = q(0, b)`, so
`dist(x, T) = |p_{T⊥} x| = |(0, b)| = |b|`, while `|x|² = |a|² + |b|² ≤ (|a| + |b|)²`. -/
theorem gwe_vfv_norm_le_first_block_add_infDist : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (x : Amb n ℓ), ‖x‖ ≤ ‖(EuclideanSpace.finAddEquivProd (q.symm x)).1‖ + infDist x (rotatedPlane q : Set (Amb n ℓ)) := by
  intro n ℓ q x
  obtain ⟨hsub, hnorm, hsurj, hproj⟩ := lip_approx_graph_coordinates n ℓ q
  -- write `q⁻¹ x = (a, b)`; its first block is `a`
  obtain ⟨a, b, hab⟩ := hsurj (q.symm x)
  have hx : x = q (graphPoint a b) := by rw [← hab, q.apply_symm_apply]
  have ha : (EuclideanSpace.finAddEquivProd (q.symm x)).1 = a := by
    rw [hab]
    ext i
    simp [graphPoint]
  -- `p_{T⊥} x = q(a, b) − q(a, 0) = q(0, b)`, so `dist(x, T) = |(0, b)| = |b|`
  have hb : infDist x (rotatedPlane q : Set (Amb n ℓ)) = ‖b‖ := by
    have h0 := hnorm 0 b
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h0
    rw [← hsNorm_starProjection_trace_identities.2.1 (n + ℓ) (rotatedPlane q) x,
      Submodule.starProjection_orthogonal_val, hx, hproj, ← map_sub, hsub, sub_self, sub_zero,
      q.norm_map]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h0
  -- `|x|² = |a|² + |b|² ≤ (|a| + |b|)²`
  have hxn : ‖x‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by rw [hx, q.norm_map, hnorm]
  rw [ha, hb]
  refine (pow_le_pow_iff_left₀ (norm_nonneg x) (add_nonneg (norm_nonneg a) (norm_nonneg b))
    two_ne_zero).1 ?_
  rw [hxn, add_sq]
  linarith [mul_nonneg (norm_nonneg a) (norm_nonneg b)]
/-- Chain rule in rotated coordinates (step 1(ii) of the vertical first variation in Simon's proof
of 4.5): for `a(y) = (finAddEquivProd (q⁻¹ y)).1`, a continuous linear map,
`D(ζ ∘ a)(x) v = Dζ(a(x)) (a v) = ⟨∇ζ(a(x)), a v⟩ = ⟨graphPoint (∇ζ(a(x))) 0, q⁻¹ v⟩
= ⟨q (graphPoint (∇ζ(a(x))) 0), v⟩`. -/
theorem gwe_vfv_hasFDerivAt_comp_first_block : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (ζ : Rn n → ℝ) (x : Amb n ℓ), DifferentiableAt ℝ ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1 → HasFDerivAt (fun y : Amb n ℓ => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1) (innerSL ℝ (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) x := by
  intro n ℓ q ζ x hζ
  -- `a = fst ∘ finAddEquivProd ∘ q⁻¹` is a continuous linear map `L`.
  let L : Amb n ℓ →L[ℝ] Rn n := (ContinuousLinearMap.fst ℝ (Rn n) (Rn ℓ)).comp
    ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).toContinuousLinearMap.comp
      q.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hL : ∀ y, L y = (EuclideanSpace.finAddEquivProd (q.symm y)).1 := fun y => rfl
  -- `⟨graphPoint w 0, z⟩ = ⟨w, (finAddEquivProd z).1⟩`: split the sum over `Fin (n + ℓ)`.
  have hcoord : ∀ (w : Rn n) (z : Amb n ℓ),
      inner ℝ (graphPoint w (0 : Rn ℓ)) z = inner ℝ w (EuclideanSpace.finAddEquivProd z).1 := by
    intro w z
    simp only [graphPoint, WithLp.ofLp_zero, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, ContinuousLinearEquiv.trans_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, WithLp.prodContinuousLinearEquiv_apply,
      PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply, Equiv.symm_symm, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right]
  -- Chain rule: `D(ζ ∘ L)(x) = Dζ(L x) ∘ L`.
  have hd : HasFDerivAt (fun y : Amb n ℓ => ζ (L y)) ((fderiv ℝ ζ (L x)).comp L) x :=
    hζ.hasFDerivAt.comp x L.hasFDerivAt
  -- `Dζ(L x) (L v) = ⟨∇ζ(L x), L v⟩ = ⟨graphPoint (∇ζ(L x)) 0, q⁻¹ v⟩ = ⟨q (graphPoint …), v⟩`.
  refine hd.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, LinearIsometryEquiv.inner_map_eq_flip,
    hcoord, gradient, InnerProductSpace.toDual_symm_apply, hL, hL]
/-- Rank-one tangential divergence (the trace computation in step (5) of Simon's proof of 4.5):
if `Df(x) = ⟨g, ·⟩`, then `div_M (f e)(x) = trace(v ↦ ⟨g, p_x v⟩ e) = ⟨g, p_x e⟩ = ⟨p_x e, p_x g⟩`,
because `p_x = p_{T_x M}` is an orthogonal projection (or `0`), hence self-adjoint and idempotent. -/
theorem gwe_vfv_divM_smul_const_eq_inner : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (f : Amb n ℓ → ℝ) (e g x : Amb n ℓ), HasFDerivAt f (innerSL ℝ g) x → V.divM (fun y => f y • e) x = inner ℝ (V.tangentProj x e) (V.tangentProj x g) := by
  intro n ℓ U V f e g x hf
  -- `⟨p u, p v⟩ = ⟨u, p v⟩` for `p = p_x`, an orthogonal projection or `0`.
  have hp : ∀ u v : Amb n ℓ,
      inner ℝ (V.tangentProj x u) (V.tangentProj x v) = inner ℝ u (V.tangentProj x v) := by
    intro u v
    rw [RectifiableVarifold.tangentProj]
    split_ifs with h
    · rw [Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ v)]
    · simp
  -- `D(f e)(x) = ⟨g, ·⟩ e`, so `D(f e)(x) ∘ p = ⟨g, p ·⟩ e` has rank one.
  have hcomp : (fderiv ℝ (fun y => f y • e) x).toLinearMap ∘ₗ (V.tangentProj x).toLinearMap =
      ((innerSL ℝ g).comp (V.tangentProj x)).toLinearMap.smulRight e := by
    rw [(hf.smul_const e).fderiv]
    refine LinearMap.ext fun w => ?_
    simp
  -- Its trace is `⟨g, p e⟩ = ⟨p g, p e⟩ = ⟨p e, p g⟩`.
  rw [RectifiableVarifold.divM, hcomp, LinearMap.trace_smulRight, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ← hp g e, real_inner_comm]
/-- Simon Ch. 5, proof of Theorem 4.5, the identity before (6) (p. 117): the defining identity 3.14
of the generalized mean curvature, localized to `B_s(0)`.  If `φ ∈ C¹`, `2r ≤ R`, `r ≤ s ≤ R`,
`B_R(0) ⊆ U` and `spt V ∩ B_R(0) ∩ spt φ ⊆ B̆_r(0)`, then
`∫_{B_s(0)} div_M(φ e) dμ_V = −∫_{B_s(0)} φ e · H dμ_V`.  Test 3.14 with `X = χ φ e ∈ C¹_c(U)`,
where the cutoff `χ` (`ρ = 2r` in `exists_smooth_cutoff_half_ball_grad_le`) is `1` on `B_r(0)`
and `0` off `B̆_{2r}(0)`.  As `div_M` is local (`Filter.EventuallyEq.fderiv_eq`),
`div_M X = 1_{B_s(0)} div_M(φ e)` and `X · H = 1_{B_s(0)} φ e · H` on `spt V`: near `x`, `χ = 1`
if `|x| < r`, `φ = 0` if `r ≤ |x| ≤ R`, and `χ = 0` if `|x| > R`.  Finally `spt V` is
`μ_V`-conull (`tdo_ghe_ae_mem_support`). -/
theorem gwe_vfv_localized_first_variation : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (φ : Amb n ℓ → ℝ) (e : Amb n ℓ) (r s R : ℝ), ContDiff ℝ 1 φ → 0 < r → 2 * r ≤ R → r ≤ s → s ≤ R → closedBall (0 : Amb n ℓ) R ⊆ U → (∀ x ∈ V.support ∩ closedBall 0 R, x ∈ tsupport φ → ‖x‖ < r) → ∫ x in closedBall (0 : Amb n ℓ) s, V.divM (fun y => φ y • e) x ∂V.weight = -∫ x in closedBall (0 : Amb n ℓ) s, φ x * inner ℝ e (H x) ∂V.weight := by
  intro n ℓ U V H hH φ e r s R hφ hr h2r hrs hsR hRU hspt
  -- The cutoff `χ ∈ C^∞` with `χ = 1` on `B_r(0)` and `χ = 0` where `|y| ≥ 2r`.
  obtain ⟨χ, hχ, -, hχ1, hχ0, -⟩ :=
    Submission.exists_smooth_cutoff_half_ball_grad_le (n + ℓ) 0 (2 * r) (by positivity)
  have hχ1' : ∀ y : Amb n ℓ, ‖y‖ ≤ r → χ y = 1 := fun y hy =>
    hχ1 y (by rw [mem_closedBall, dist_zero_right]; linarith)
  have hχ0' : ∀ y : Amb n ℓ, 2 * r ≤ ‖y‖ → χ y = 0 := fun y hy =>
    hχ0 y (by rwa [dist_zero_right])
  -- The test field `X = χ φ e ∈ C¹_c(U)`, supported in `B_{2r}(0) ⊆ B_R(0) ⊆ U`.
  set X : Amb n ℓ → Amb n ℓ := fun y => (χ y * φ y) • e with hX_def
  have hX : ContDiff ℝ 1 X :=
    ((hχ.of_le (by exact_mod_cast le_top)).mul hφ).smul contDiff_const
  have hX_supp : tsupport X ⊆ closedBall 0 (2 * r) := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    exact hy (by simp only [hX_def, hχ0' y (by linarith), zero_mul, zero_smul])
  have hXc : HasCompactSupport X :=
    (isCompact_closedBall 0 (2 * r)).of_isClosed_subset (isClosed_tsupport X) hX_supp
  have hXU : tsupport X ⊆ U :=
    hX_supp.trans ((closedBall_subset_closedBall (by linarith)).trans hRU)
  -- The first variation formula 3.14 for `X`.
  have hfv := hH.2 X hX hXc hXU
  -- `div_M Y (x)` only depends on `Y` near `x`, and `div_M 0 = 0`.
  have hloc : ∀ (Y Z : Amb n ℓ → Amb n ℓ) (x : Amb n ℓ), Y =ᶠ[𝓝 x] Z →
      V.divM Y x = V.divM Z x := fun Y Z x h => by
    simp only [RectifiableVarifold.divM, h.fderiv_eq (𝕜 := ℝ)]
  have hzero : ∀ x : Amb n ℓ, V.divM (fun _ => 0) x = 0 := fun x => by
    simp [RectifiableVarifold.divM]
  -- On `spt V`: `div_M X = 1_{B_s(0)} div_M(φ e)` and `X · H = 1_{B_s(0)} φ e · H`.
  have hpt : ∀ x ∈ V.support,
      V.divM X x =
        (closedBall (0 : Amb n ℓ) s).indicator (fun x => V.divM (fun y => φ y • e) x) x ∧
      inner ℝ (X x) (H x) =
        (closedBall (0 : Amb n ℓ) s).indicator (fun x => φ x * inner ℝ e (H x)) x := by
    intro x hx
    rcases lt_or_ge ‖x‖ r with h1 | h1
    · -- `|x| < r`: `X = φ e` on the neighbourhood `B̆_r(0)` of `x`, and `x ∈ B_s(0)`.
      have hxs : x ∈ closedBall (0 : Amb n ℓ) s := by
        rw [mem_closedBall, dist_zero_right]; linarith
      have hev : X =ᶠ[𝓝 x] fun y => φ y • e := by
        have hxr : x ∈ ball (0 : Amb n ℓ) r := by rwa [mem_ball, dist_zero_right]
        filter_upwards [isOpen_ball.mem_nhds hxr] with y hy
        rw [mem_ball, dist_zero_right] at hy
        simp only [hX_def, hχ1' y hy.le, one_mul]
      rw [indicator_of_mem hxs, indicator_of_mem hxs]
      refine ⟨hloc _ _ x hev, ?_⟩
      simp only [hX_def, hχ1' x h1.le, one_mul, real_inner_smul_left]
    · rcases le_or_gt ‖x‖ R with h2 | h2
      · -- `r ≤ |x| ≤ R`: `x ∉ spt φ`, so `φ = 0` near `x`.
        have hφx : x ∉ tsupport φ := fun h =>
          absurd (hspt x ⟨hx, by rwa [mem_closedBall, dist_zero_right]⟩ h) (not_lt.2 h1)
        have hφ0 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hφx
        have hX0 : X =ᶠ[𝓝 x] fun _ => 0 := hφ0.mono fun y hy => by simp [hX_def, hy]
        have hφe0 : (fun y => φ y • e) =ᶠ[𝓝 x] fun _ => 0 := hφ0.mono fun y hy => by simp [hy]
        have hφx0 : φ x = 0 := hφ0.self_of_nhds
        refine ⟨?_, ?_⟩
        · rw [hloc _ _ x hX0, hzero]
          by_cases hxs : x ∈ closedBall (0 : Amb n ℓ) s
          · rw [indicator_of_mem hxs, hloc _ _ x hφe0, hzero]
          · rw [indicator_of_notMem hxs]
        · rw [indicator_apply_eq_zero.2 fun _ => by simp only [hφx0, zero_mul]]
          simp [hX_def, hφx0]
      · -- `|x| > R ≥ 2r`: `χ = 0` near `x`, and `x ∉ B_s(0)`.
        have hxs : x ∉ closedBall (0 : Amb n ℓ) s := by
          rw [mem_closedBall, dist_zero_right]; linarith
        have hX0 : X =ᶠ[𝓝 x] fun _ => 0 := by
          have hxR : x ∈ {y : Amb n ℓ | R < ‖y‖} := h2
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hxR] with y hy
          have hy' : R < ‖y‖ := hy
          simp [hX_def, hχ0' y (by linarith)]
        rw [indicator_of_notMem hxs, indicator_of_notMem hxs]
        refine ⟨by rw [hloc _ _ x hX0, hzero], ?_⟩
        simp [hX_def, hχ0' x (by linarith)]
  -- `μ_V`-a.e. point lies in `spt V`; integrate the pointwise identities.
  have hae := Submission.tdo_ghe_ae_mem_support n ℓ U V
  calc ∫ x in closedBall (0 : Amb n ℓ) s, V.divM (fun y => φ y • e) x ∂V.weight
      = ∫ x, (closedBall (0 : Amb n ℓ) s).indicator
          (fun x => V.divM (fun y => φ y • e) x) x ∂V.weight :=
        (integral_indicator measurableSet_closedBall).symm
    _ = ∫ x, V.divM X x ∂V.weight :=
        integral_congr_ae (hae.mono fun x hx => (hpt x hx).1.symm)
    _ = -∫ x, inner ℝ (X x) (H x) ∂V.weight := hfv
    _ = -∫ x, (closedBall (0 : Amb n ℓ) s).indicator
          (fun x => φ x * inner ℝ e (H x)) x ∂V.weight := by
        rw [integral_congr_ae (hae.mono fun x hx => (hpt x hx).2)]
    _ = -∫ x in closedBall (0 : Amb n ℓ) s, φ x * inner ℝ e (H x) ∂V.weight := by
        rw [integral_indicator measurableSet_closedBall]
/-- Simon Ch. 5, proof of Theorem 4.5, displays (5), (6) and the curvature term of (8)
(pp. 117–118), in the rotated frame `T = q(ℝⁿ × {0})`: with `e'_j = q(0, e_j)`, `a(x)` the first
block of `q⁻¹x` and `g(x) = q(∇ζ(a(x)), 0)`,
`|∫_{B_{σ/2}(0)} p_x e'_j · p_x g(x) dμ_V| ≤ M (σ/4) ∫_{B_{σ/2}(0)} |H| dμ_V`.
`ζ̃ = ζ ∘ a` has `Dζ̃(x) = ⟨g(x), ·⟩`, so the integrand is `div_M(ζ̃ e'_j)`.  On
`spt V ∩ B_σ(0) ∩ tsupport ζ̃`, `|x| ≤ |a(x)| + dist(x, T) < σ/4 + σ/16 = 5σ/16`, so the first
variation formula localizes to `B_{σ/2}(0)`; then `|ζ| ≤ Mσ/4`, `|e'_j| = 1` and the integrability
of `|H|` on the compact `B_{σ/2}(0) ⊆ U` bound the curvature term. -/
theorem gwe_vertical_first_variation : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ σ : ℝ, 0 < σ → closedBall 0 σ ⊆ U → ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, (∀ x ∈ V.support ∩ closedBall 0 σ, infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ σ / 16) → ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in closedBall (0 : Amb n ℓ) (σ / 2), inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))) (V.tangentProj x (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) ∂V.weight| ≤ M * (σ / 4) * ∫ x in closedBall (0 : Amb n ℓ) (σ / 2), ‖H x‖ ∂V.weight := by
  intro n ℓ hn U _hU V H hH σ hσ hσU q hheight ζ hζ _hζc hζσ M hM j
  -- `ζ̃ = ζ ∘ a` is `C¹`, since `a(y) = (q⁻¹y)₁` is continuous linear.
  have ha : Continuous fun y : Amb n ℓ => (EuclideanSpace.finAddEquivProd (q.symm y)).1 :=
    continuous_fst.comp (EuclideanSpace.finAddEquivProd.continuous.comp q.symm.continuous)
  have hζ' : ContDiff ℝ 1 fun y : Amb n ℓ => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1 :=
    hζ.comp (contDiff_fst.comp (EuclideanSpace.finAddEquivProd.contDiff.comp q.symm.contDiff))
  have hζd : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
  -- The integrand is `div_M(ζ̃ e'_j)`: `Dζ̃(x) = ⟨g(x), ·⟩`, and the trace of the rank-one map.
  have hdiv : ∀ x, inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) =
      V.divM (fun y => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1 •
        q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))) x := fun x =>
    (Submission.gwe_vfv_divM_smul_const_eq_inner n ℓ U V _ _ _ x
      (Submission.gwe_vfv_hasFDerivAt_comp_first_block n ℓ q ζ x (hζd _))).symm
  -- Localization: on `spt V ∩ B_σ(0) ∩ tsupport ζ̃`, `|x| ≤ |a(x)| + dist(x, T) < σ/4 + σ/16`.
  have hloc : ∀ x ∈ V.support ∩ closedBall 0 σ,
      x ∈ tsupport (fun y : Amb n ℓ => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1) →
      ‖x‖ < 5 * σ / 16 := by
    intro x hx hxζ
    have h₁ : ‖(EuclideanSpace.finAddEquivProd (q.symm x)).1‖ < σ / 4 :=
      mem_ball_zero_iff.1 (hζσ (tsupport_comp_subset_preimage ζ ha hxζ))
    linarith [hheight x hx, Submission.gwe_vfv_norm_le_first_block_add_infDist n ℓ q x]
  -- The first variation formula on `B_{σ/2}(0)`, with `r = 5σ/16` and `R = σ`.
  simp only [hdiv]
  rw [Submission.gwe_vfv_localized_first_variation n ℓ U V H hH _ _ (5 * σ / 16) (σ / 2) σ hζ'
      (by positivity) (by linarith) (by linarith) (by linarith) hσU hloc, abs_neg,
    ← Real.norm_eq_abs, ← integral_const_mul]
  -- `|ζ| ≤ Mσ/4`, `|e'_j| = 1`, and `|H|` is integrable on the compact `B_{σ/2}(0) ⊆ U`.
  have hζM : ∀ y, |ζ y| ≤ M * (σ / 4) :=
    Submission.gwe_vfv_abs_le_grad_bound_mul_radius n hn ζ (σ / 4) M (by positivity) hζd hζσ hM
  have he : ‖q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))‖ = 1 := by
    rw [q.norm_map, ← Real.sqrt_sq (norm_nonneg _),
      (Submission.lip_approx_graph_coordinates n ℓ q).2.1]
    simp
  have hH' : IntegrableOn H (closedBall 0 (σ / 2)) V.weight :=
    hH.1.integrableOn_compact_subset ((closedBall_subset_closedBall (by linarith)).trans hσU)
      (isCompact_closedBall 0 _)
  refine norm_integral_le_of_norm_le (hH'.norm.const_mul _) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hζM _) ((abs_real_inner_le_norm _ _).trans_eq (by rw [he, one_mul]))
    (abs_nonneg _) ((abs_nonneg _).trans (hζM 0))

/-- Simon Ch. 5, proof of Theorem 4.5, (8)–(12) on the varifold side. Let `f` be `1`-Lipschitz on
`Bⁿ_{σ/2}(0)` with `|f| ≤ σ/16`, let `spt V ∩ B_σ(0)` lie within `σ/16` of `T = q(ℝⁿ × {0})`, and
let `p_x` be the graph plane of `Df(x')` at `μ_V`-a.e. `x = q(x', f x')` with `|x'| < σ/2` and `f`
differentiable at `x'`. For `ζ ∈ C¹_c(B̆ⁿ_{σ/4}(0))` with `|∇ζ| ≤ M`, `a(x)` the first `n`
coordinates of `q⁻¹x`,
`Γ = q(graph f|B_{σ/2})` and `Γ' = q(graph f|B̆_{σ/4})`,
`|∫_{Γ'} ∇fʲ(a x) · ∇ζ(a x) dμ_V| ≤ M μ_V(B_{σ/2}(0) ∩ (spt V \ Γ)) + M ∫_{B_σ(0)} |p_x − p_T|² dμ_V
  + M (σ/4) ∫_{B_{σ/2}(0)} |H| dμ_V`.
The integrand `Φ(x) = p_x e'_j · p_x q(∇ζ(a x), 0)` of the vertical first variation satisfies
`|∫_{B_{σ/2}(0)} Φ| ≤ M (σ/4) ∫ |H|` and `|Φ| ≤ M`. It vanishes at points of `Γ \ Γ'`, where
`∇ζ(a x) = 0`, and `B_{σ/2}(0) \ (Γ ∪ Γ')` has weight at most `μ_V(B_{σ/2}(0) ∩ (spt V \ Γ))`,
since `μ_V((spt V)ᶜ) = 0`. By the area formula and Rademacher's theorem, the points of `Γ'` over
non-differentiability points of `f` form an `Hⁿ`-null, hence `μ_V`-null, set. At `μ_V`-a.e. other
point of `Γ'`, the tilt algebra gives `|Φ − ∇fʲ · ∇ζ| ≤ M |p_x − p_T|²`; integrate over `Γ'`. -/
theorem gwe_graph_tangential_estimate : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → ∀ σ : ℝ, 0 < σ → closedBall 0 σ ⊆ U → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ), LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → (∀ x ∈ closedBall (0 : Rn n) (σ / 2), ‖f x‖ ≤ σ / 16) → (∀ x ∈ V.support ∩ closedBall 0 σ, infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ σ / 16) → (∀ᵐ x ∂V.weight, ∀ x' ∈ ball (0 : Rn n) (σ / 2), x = q (graphPoint x' (f x')) → DifferentiableAt ℝ f x' → V.tangentProj x = (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (fderiv ℝ f x' v)))).starProjection) → ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in q '' graphOver f (ball 0 (σ / 4)), inner ℝ (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1) (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) ∂V.weight| ≤ M * (V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2))))).toReal + M * ∫ x in closedBall 0 σ, hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight + M * (σ / 4) * ∫ x in closedBall 0 (σ / 2), ‖H x‖ ∂V.weight := by
  intro n ℓ hn U hU V H hH hpm σ hσ hσU q f hf hfb hdist htan ζ hζ hζc hζs M hM j
  obtain ⟨hfin, hcompl, hnull⟩ := Submission.gte_weight_null_finite n ℓ U V
  obtain ⟨hproj, hint⟩ := Submission.gte_tangentProj_integrands n ℓ U V
  obtain ⟨hgpc, hac, hagp, himg⟩ := Submission.gte_graph_image_geometry n ℓ q
  obtain ⟨hZm, hZ0, hDf⟩ := Submission.gte_lipschitz_ball_calculus n ℓ f 1 (σ / 2) hf
  obtain ⟨hsub, hnorm, -, -⟩ := lip_approx_graph_coordinates n ℓ q
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- Step 1: `|q(w, 0)| = |w|`, `|e'_j| = 1`, `(0, 0) = 0` and `|A|² ≥ 0`
  have hgp0 : ∀ w : Rn n, ‖q (graphPoint w (0 : Rn ℓ))‖ = ‖w‖ := by
    intro w
    have h := hnorm w 0
    rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
    rw [LinearIsometryEquiv.norm_map]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  have he : ‖q (graphPoint (0 : Rn n) (EuclideanSpace.single j (1 : ℝ)))‖ = 1 := by
    have h := hnorm 0 (EuclideanSpace.single j (1 : ℝ))
    have h1 : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
    rw [norm_zero, zero_pow two_ne_zero, zero_add, h1] at h
    rw [LinearIsometryEquiv.norm_map]
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h
  have hgp00 : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    have h := hsub 0 0 0 0
    simp only [sub_self] at h
    exact h.symm
  have hψ0 : ∀ A : Amb n ℓ →L[ℝ] Amb n ℓ, 0 ≤ hsNormSq A := fun A =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  -- Step 2: `Γ` is compact, `Γ'` is Borel, `Γ' ⊆ B_{σ/2}(0)`, and `μ_V(B_σ(0)) < ∞`
  obtain ⟨hΓc, hΓ'm⟩ := himg f (σ / 2) (σ / 4) hf.continuousOn (by linarith)
  have hΓm : MeasurableSet (q '' graphOver f (closedBall 0 (σ / 2))) := hΓc.measurableSet
  have hBσ : closedBall (0 : Amb n ℓ) (σ / 2) ⊆ closedBall 0 σ :=
    closedBall_subset_closedBall (by linarith)
  have hμB : V.weight (closedBall (0 : Amb n ℓ) (σ / 2)) < ⊤ :=
    hfin _ (isCompact_closedBall 0 _) (hBσ.trans hσU)
  have hμBσ : V.weight (closedBall (0 : Amb n ℓ) σ) < ⊤ :=
    hfin _ (isCompact_closedBall 0 _) hσU
  have hΓ'B : q '' graphOver f (ball 0 (σ / 4)) ⊆ closedBall (0 : Amb n ℓ) (σ / 2) := by
    rintro _ ⟨_, ⟨x', hx', rfl⟩, rfl⟩
    have hx'n : ‖x'‖ < σ / 4 := mem_ball_zero_iff.mp hx'
    have hfx : ‖f x'‖ ≤ σ / 16 :=
      hfb x' (ball_subset_closedBall (ball_subset_ball (by linarith) hx'))
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    -- `|(x', f x')|² = |x'|² + |f x'|² ≤ σ²/16 + σ²/256 ≤ σ²/4`
    have h2 : ‖graphPoint x' (f x')‖ ^ 2 ≤ (σ / 2) ^ 2 := by
      rw [hnorm]
      nlinarith [mul_le_mul hx'n.le hx'n.le (norm_nonneg _) (by linarith),
        mul_le_mul hfx hfx (norm_nonneg _) (by linarith), sq_nonneg σ]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).mp h2
  -- Step 3: the first-variation integrand `Φ` is bounded by `M` and integrable on `B_{σ/2}(0)`
  have hgrad : Continuous (gradient ζ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hζ.continuous_fderiv one_ne_zero)
  have hgcont : Continuous fun x : Amb n ℓ =>
      q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) (0 : Rn ℓ)) := by
    have hgp0c : Continuous fun w : Rn n => graphPoint w (0 : Rn ℓ) :=
      hgpc.comp (continuous_id.prodMk continuous_const)
    exact q.continuous.comp (hgp0c.comp (hgrad.comp hac))
  have hΦint : IntegrableOn (fun x => inner ℝ
      (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))))
      (closedBall 0 (σ / 2)) V.weight :=
    (hint hpm _ hμB).1 _ _ M hgcont.aestronglyMeasurable fun x => (hgp0 _).trans_le (hM _)
  have hΦle : ∀ x, |inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0)))| ≤ M := by
    intro x
    calc _ ≤ ‖V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))‖ *
          ‖V.tangentProj x
            (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))‖ *
          ‖q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0)‖ :=
          mul_le_mul (hproj _ _) (hproj _ _) (norm_nonneg _) (norm_nonneg _)
      _ ≤ 1 * M := by
          rw [he, hgp0]
          exact mul_le_mul_of_nonneg_left (hM _) zero_le_one
      _ = M := one_mul M
  -- Step 4: `Φ = 0` at the points of `Γ` outside `Γ'`, where `∇ζ(a x) = 0`
  have hΦzero : ∀ x ∈ (closedBall (0 : Amb n ℓ) (σ / 2) \ q '' graphOver f (ball 0 (σ / 4))) ∩
      q '' graphOver f (closedBall 0 (σ / 2)),
      inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
        (V.tangentProj x
          (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) = 0 := by
    rintro x ⟨⟨-, hxG'⟩, ⟨_, ⟨x', -, rfl⟩, rfl⟩⟩
    have hx' : x' ∉ tsupport ζ := fun h => hxG' ⟨_, ⟨x', hζs h, rfl⟩, rfl⟩
    have hgrad0 : gradient ζ x' = 0 := by
      rw [gradient, fderiv_of_notMem_tsupport ℝ hx', map_zero]
    rw [hagp, hgrad0, hgp00, map_zero, map_zero, inner_zero_right]
  -- Step 5: off `Γ ∪ Γ'`, `B_{σ/2}(0)` has weight at most `μ_V(B_{σ/2}(0) ∩ (spt V \ Γ)) < ∞`
  have hmle : V.weight ((closedBall (0 : Amb n ℓ) (σ / 2) \ q '' graphOver f (ball 0 (σ / 4))) \
      q '' graphOver f (closedBall 0 (σ / 2))) ≤
      V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) := by
    calc _ ≤ V.weight ((closedBall 0 (σ / 2) ∩
          (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) ∪ V.supportᶜ) := by
          refine measure_mono fun x hx => ?_
          by_cases hs : x ∈ V.support
          · exact Or.inl ⟨hx.1.1, hs, hx.2⟩
          · exact Or.inr hs
      _ ≤ _ + V.weight V.supportᶜ := measure_union_le _ _
      _ = _ := by rw [hcompl, add_zero]
  have hmlt : V.weight (closedBall (0 : Amb n ℓ) (σ / 2) ∩
      (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) < ⊤ :=
    (measure_mono inter_subset_left).trans_lt hμB
  -- Step 6: `φ = ∇fʲ(a x) · ∇ζ(a x)` is Borel, and the tilt integrand is integrable on `B_σ(0)`
  have hφm : AEStronglyMeasurable (fun x => inner ℝ
      (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1)
      (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1))
      (V.weight.restrict (q '' graphOver f (ball 0 (σ / 4)))) := by
    have h1 : Measurable (gradient fun y => f y j) :=
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)
    exact (Continuous.measurable2 (c := fun a b : Rn n => inner ℝ a b) continuous_inner
      (h1.comp hac.measurable) (hgrad.measurable.comp hac.measurable)).aestronglyMeasurable
  have hψint : IntegrableOn (fun x => hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection))
      (closedBall 0 σ) V.weight :=
    (hint hpm _ hμBσ).2 _
  -- Step 7: the graph over the non-differentiability points of `f` is `Hⁿ`-null (area formula
  -- and Rademacher), hence `μ_V`-null
  have hZnull : V.weight (q '' graphOver f (ball (0 : Rn n) (σ / 2) ∩
      {x | ¬DifferentiableAt ℝ f x})) = 0 := by
    apply hnull
    have h := gwe_lipschitz_graph_area_formula n ℓ hn q f 1 (σ / 2) hf _ hZm
      (inter_subset_left.trans ball_subset_closedBall) (fun _ => 1)
    rw [setLIntegral_one, setLIntegral_measure_zero _ _ hZ0] at h
    exact h
  -- Step 8: a.e. on `Γ'`, `p_x` is the graph plane of `Df(a x)`, and the tilt algebra gives
  -- `|Φ - φ| ≤ |p_x - p_T|² |∇ζ(a x)| ≤ M |p_x - p_T|²`
  have hae : ∀ᵐ x ∂V.weight, x ∈ q '' graphOver f (ball 0 (σ / 4)) →
      |inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
        (V.tangentProj x
          (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) -
        inner ℝ (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1)
          (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1)| ≤
        M * hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) := by
    filter_upwards [htan, measure_eq_zero_iff_ae_notMem.mp hZnull] with x hxt hxZ hxG'
    obtain ⟨_, ⟨x', hx', rfl⟩, rfl⟩ := hxG'
    have hx'2 : x' ∈ ball (0 : Rn n) (σ / 2) := ball_subset_ball (by linarith) hx'
    have hd : DifferentiableAt ℝ f x' := by
      by_contra hnd
      exact hxZ ⟨_, ⟨x', ⟨hx'2, hnd⟩, rfl⟩, rfl⟩
    obtain ⟨hD1, hgradf⟩ := hDf x' hx'2
    have hD : ‖fderiv ℝ f x'‖ ≤ 1 := by exact_mod_cast hD1
    have hTA := (Submission.gwe_graph_tilt_algebra n ℓ q (fderiv ℝ f x') hD).2 j _
      (gradient ζ x') (hgradf hd j)
    rw [hagp, hxt x' hx'2 rfl hd]
    exact hTA.trans ((mul_le_mul_of_nonneg_left (hM _) (hψ0 _)).trans_eq (mul_comm _ _))
  -- Step 9: combine the localized comparison with the vertical first-variation bound
  have hcmp := Submission.gte_localized_comparison V.weight (closedBall (0 : Amb n ℓ) (σ / 2))
    (closedBall 0 σ) (q '' graphOver f (closedBall 0 (σ / 2))) (q '' graphOver f (ball 0 (σ / 4)))
    (fun x => inner ℝ (V.tangentProj x (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))))
      (V.tangentProj x
        (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))))
    (fun x => inner ℝ (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1)
      (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1))
    (fun x => hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection)) M
    (V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))))
    hM0 hΓm hΓ'm hΓ'B (hΓ'B.trans hBσ) hΦint hΦle hΦzero hmle hmlt hφm hψint (fun _ => hψ0 _) hae
  have hfv := Submission.gwe_vertical_first_variation n ℓ hn U hU V H hH σ hσ hσU q hdist ζ hζ
    hζc hζs M hM j
  linarith
/-- **Derivative bounds for a map that is `1`-Lipschitz on a closed ball** (Simon Ch. 5, proof of
4.5, (14)–(16), first step).  Let `f : ℝⁿ → ℝ^ℓ` be `1`-Lipschitz on `B_r(0)`, `|Df|² = hsNormSq Df`
and `fʲ = (f ·)_j`.  `x ↦ Df(x)` is measurable (`measurable_fderiv`) and `A ↦ |A|²` is continuous,
so `|Df|²` is measurable; so is `∇fʲ = (toDual)⁻¹ ∘ Dfʲ`.  `B_r(0)` is a neighbourhood of each point
of `B̆_r(0)`, so `‖Df‖ ≤ 1` there (`norm_fderiv_le_of_lipschitzOn`) and `|Df|² ≤ n`; each `fʲ` is
`1`-Lipschitz on `B_r(0)` as well (`|w_j| ≤ |w|`), so `|∇fʲ| = ‖Dfʲ‖ ≤ 1` on `B̆_r(0)`.  By
Rademacher's theorem `f` is differentiable at a.e. `x ∈ B̆_r(0)`; there `Dfʲ(x) = π_j ∘ Df(x)`, so
`|∇fʲ(x)|² = Σᵢ ((Df(x) eᵢ)_j)² ≤ Σᵢ |Df(x) eᵢ|² = |Df(x)|²`. -/
theorem gwe_wewe_lipschitz_fderiv_facts : ∀ (n ℓ : ℕ) (r : ℝ) (f : Rn n → Rn ℓ), LipschitzOnWith 1 f (closedBall 0 r) → Measurable (fun x => hsNormSq (fderiv ℝ f x)) ∧ (∀ j : Fin ℓ, Measurable (gradient (fun y => f y j))) ∧ (∀ x, 0 ≤ hsNormSq (fderiv ℝ f x)) ∧ (∀ x ∈ ball (0 : Rn n) r, hsNormSq (fderiv ℝ f x) ≤ n ∧ ∀ j : Fin ℓ, ‖gradient (fun y => f y j) x‖ ≤ 1) ∧ ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 r → ∀ j : Fin ℓ, ‖gradient (fun y => f y j) x‖ ^ 2 ≤ hsNormSq (fderiv ℝ f x) := by
  intro n ℓ r f hf
  -- `B_r(0)` is a neighbourhood of every point of the open ball.
  have hnhds : ∀ x ∈ ball (0 : Rn n) r, closedBall (0 : Rn n) r ∈ 𝓝 x := fun x hx =>
    Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall
  -- Each coordinate `fʲ` is `1`-Lipschitz on `B_r(0)`, since `|w_j| ≤ |w|`.
  have hfj : ∀ j : Fin ℓ, LipschitzOnWith 1 (fun y => f y j) (closedBall 0 r) := by
    intro j
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    calc dist (f y j) (f z j) ≤ dist (f y) (f z) := PiLp.dist_apply_le _ _ _
      _ ≤ (1 : ℝ≥0) * dist y z := hf.dist_le_mul y hy z hz
  -- `|∇g(x)|² = Σᵢ (Dg(x) eᵢ)²`, since `(∇g(x))ᵢ = ⟪∇g(x), eᵢ⟫ = Dg(x) eᵢ`.
  have hgrad : ∀ (g : Rn n → ℝ) (x : Rn n),
      ‖gradient g x‖ ^ 2 = ∑ i, (fderiv ℝ g x (EuclideanSpace.single i 1)) ^ 2 := by
    intro g x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Rn n)
      (x := EuclideanSpace.single i 1) (y := fderiv ℝ g x)
    rw [EuclideanSpace.inner_single_right] at h
    rw [Real.norm_eq_abs, sq_abs]
    simpa [gradient] using congrArg (· ^ 2) h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `|Df|²` is a continuous function of the measurable map `x ↦ Df(x)`.
    have hcont : Continuous fun A : Rn n →L[ℝ] Rn ℓ => hsNormSq A := by
      unfold hsNormSq
      fun_prop
    exact hcont.measurable.comp (measurable_fderiv ℝ f)
  · intro j
    exact (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ (fun y => f y j))
  · intro x
    unfold hsNormSq
    positivity
  · intro x hx
    refine ⟨?_, fun j => ?_⟩
    · -- `‖Df(x) eᵢ‖ ≤ ‖Df(x)‖ ‖eᵢ‖ ≤ 1` for each of the `n` summands.
      have h1 : ‖fderiv ℝ f x‖ ≤ 1 := by
        simpa using norm_fderiv_le_of_lipschitzOn ℝ (hnhds x hx) hf
      unfold hsNormSq
      calc ∑ i : Fin n, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2
          ≤ ∑ _i : Fin n, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have : ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤ 1 := by
              calc _ ≤ ‖fderiv ℝ f x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
                    (fderiv ℝ f x).le_opNorm _
                _ ≤ 1 := by simpa using h1
            exact pow_le_one₀ (norm_nonneg _) this
        _ = n := by simp
    · -- The Riesz map `toDual` is an isometry, so `|∇fʲ(x)| = ‖Dfʲ(x)‖ ≤ 1`.
      have h1 : ‖fderiv ℝ (fun y => f y j) x‖ ≤ 1 := by
        simpa using norm_fderiv_le_of_lipschitzOn ℝ (hnhds x hx) (hfj j)
      simpa [gradient] using h1
  · -- Rademacher: `f` is differentiable within `B_r(0)`, hence at `x`, for a.e. `x ∈ B̆_r(0)`.
    filter_upwards [hf.ae_differentiableWithinAt_of_mem (μ := volume)] with x hx hxb j
    have hd : DifferentiableAt ℝ f x :=
      (hx (ball_subset_closedBall hxb)).differentiableAt (hnhds x hxb)
    have hfd : fderiv ℝ (fun y => f y j) x =
        (EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).comp (fderiv ℝ f x) :=
      ((EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
    rw [hgrad, hfd]
    unfold hsNormSq
    refine Finset.sum_le_sum fun i _ => ?_
    rw [ContinuousLinearMap.comp_apply, ← sq_abs]
    have h := PiLp.norm_apply_le (fderiv ℝ f x (EuclideanSpace.single i 1)) j
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
/-- Energy bound behind Simon Ch. 5, 4.5 (16), with the explicit constant `C_E = (1 + n) K0`.
Let `f : ℝⁿ → ℝ^ℓ` be `1`-Lipschitz on `closedBall 0 (σ / 2)`, `B1 = ball 0 (3σ/8)`, and `W`
measurable with `W = 0 ∨ 1 ≤ W` a.e. on `B1`, `Lⁿ(B1 ∩ {W = 0}) ≤ K0 E σⁿ` and
`∫⁻_{B1} |Df|² W ≤ K0 E σⁿ`.  Then `|Df|²` is integrable on `B1` and
`∫_{B1} |Df|² ≤ (1 + n) K0 E σⁿ`.
Since `0 ≤ |Df|² ≤ n` on `B1` (`lipschitz_fderiv_facts`), a.e. on `B1` we have
`|Df|² ≤ |Df|² W + n 1_{B1 ∩ {W = 0}}`; integrate and use the two hypotheses. -/
theorem gwe_wewe_energy_bound : ∀ (n ℓ : ℕ) (K0 σ E : ℝ) (f : Rn n → Rn ℓ) (W : Rn n → ℝ), 0 ≤ K0 → 0 < σ → 0 ≤ E → LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → Measurable W → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨ 1 ≤ W x) → volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → ∫⁻ x in ball (0 : Rn n) (3 * σ / 8), ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) (ball (0 : Rn n) (3 * σ / 8)) ∧ ∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x) ≤ (1 + n) * K0 * E * σ ^ n := by
  intro n ℓ K0 σ E f W hK0 hσ hE hf hW hW01 hN hWE
  -- Step 1: `lipschitz_fderiv_facts` with `r = σ / 2`; since `B1 ⊆ ball 0 (σ / 2)`,
  -- `0 ≤ |Df|² ≤ n` on `B1`.
  obtain ⟨hmeas, -, hnonneg, hbound, -⟩ :=
    Submission.gwe_wewe_lipschitz_fderiv_facts n ℓ (σ / 2) f hf
  set B1 : Set (Rn n) := ball (0 : Rn n) (3 * σ / 8)
  have hB1meas : MeasurableSet B1 := measurableSet_ball
  have hle : ∀ x ∈ B1, hsNormSq (fderiv ℝ f x) ≤ n := fun x hx =>
    (hbound x (ball_subset_ball (by linarith) hx)).1
  -- Step 2: `|Df|²` is measurable and bounded on the finite-measure ball `B1`.
  have hint : IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) B1 := by
    refine Measure.integrableOn_of_bounded (M := n) measure_ball_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hB1meas] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    exact hle x hx
  refine ⟨hint, ?_⟩
  -- Step 3: `N = B1 ∩ {W = 0}` is a measurable subset of `B1`.
  set N : Set (Rn n) := B1 ∩ {x | W x = 0}
  have hNmeas : MeasurableSet N := hB1meas.inter (hW (measurableSet_singleton 0))
  have hNsub : N ⊆ B1 := inter_subset_left
  have ha : 0 ≤ K0 * E * σ ^ n := by positivity
  -- Step 4: a.e. on `B1`, `ofReal |Df|² ≤ ofReal (|Df|² W) + 1_N ofReal n`;
  -- split into the cases `W = 0` and `1 ≤ W`.
  have hpt : ∀ᵐ x ∂(volume.restrict B1), ENNReal.ofReal (hsNormSq (fderiv ℝ f x)) ≤
      ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x) +
        N.indicator (fun _ => ENNReal.ofReal n) x := by
    rw [ae_restrict_iff' hB1meas]
    filter_upwards [hW01] with x hx hxB
    rcases hx hxB with h0 | h1
    · rw [indicator_of_mem (show x ∈ N from ⟨hxB, h0⟩)]
      exact le_add_left (ENNReal.ofReal_le_ofReal (hle x hxB))
    · refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
      calc hsNormSq (fderiv ℝ f x) = hsNormSq (fderiv ℝ f x) * 1 := (mul_one _).symm
        _ ≤ hsNormSq (fderiv ℝ f x) * W x := mul_le_mul_of_nonneg_left h1 (hnonneg x)
  -- Step 5: integrate over `B1`; (H3) and (H2) bound the two terms.
  have hlint : ∫⁻ x in B1, ENNReal.ofReal (hsNormSq (fderiv ℝ f x)) ≤
      ENNReal.ofReal ((1 + n) * K0 * E * σ ^ n) := by
    calc ∫⁻ x in B1, ENNReal.ofReal (hsNormSq (fderiv ℝ f x))
        ≤ ∫⁻ x in B1, (ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x) +
            N.indicator (fun _ => ENNReal.ofReal n) x) := lintegral_mono_ae hpt
      _ = (∫⁻ x in B1, ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x)) +
            ENNReal.ofReal n * volume N := by
          rw [lintegral_add_right _ (measurable_const.indicator hNmeas),
            lintegral_indicator_const hNmeas, Measure.restrict_apply hNmeas,
            inter_eq_left.mpr hNsub]
      _ ≤ ENNReal.ofReal (K0 * E * σ ^ n) + ENNReal.ofReal n * ENNReal.ofReal (K0 * E * σ ^ n) := by
          gcongr
      _ = ENNReal.ofReal ((1 + n) * K0 * E * σ ^ n) := by
          rw [← ENNReal.ofReal_mul (Nat.cast_nonneg n),
            ← ENNReal.ofReal_add ha (mul_nonneg (Nat.cast_nonneg n) ha)]
          congr 1
          ring
  -- Step 6: `∫_{B1} |Df|² = (∫⁻_{B1} ofReal |Df|²).toReal ≤ (1 + n) K0 E σⁿ`.
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnonneg) hmeas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlint
/-- Cauchy–Schwarz on a set of finite measure (Hölder with `p = q = 2` for `g` and `1` on
`ν = μ|_S`): if `0 ≤ g` and `g² ≤ D` a.e. on `S`, with `D` integrable on `S`, then
`∫_S g dμ ≤ (∫_S g² dμ)^{1/2} μ(S)^{1/2} ≤ μ(S)^{1/2} (∫_S D dμ)^{1/2}`. -/
theorem gwe_wewe_setIntegral_le_sqrt_mul_sqrt : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (S : Set X) (g D : X → ℝ), μ S < ⊤ → AEStronglyMeasurable g (μ.restrict S) → IntegrableOn D S μ → (∀ᵐ x ∂(μ.restrict S), 0 ≤ g x ∧ g x ^ 2 ≤ D x) → ∫ x in S, g x ∂μ ≤ Real.sqrt (μ S).toReal * Real.sqrt (∫ x in S, D x ∂μ) := by
  intro X _ μ S g D hS hg hD hgD
  -- `ν = μ|_S` is a finite measure.
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  -- `g²` is `ν`-integrable, being dominated by the integrable `D`.
  have hg2 : Integrable (fun x => g x ^ 2) (μ.restrict S) :=
    Integrable.mono' hD (hg.pow 2)
      (hgD.mono fun x hx => (Real.norm_of_nonneg (sq_nonneg (g x))).le.trans hx.2)
  -- Hence `g ∈ L²(ν)`.
  have hgL2 : MemLp g (ENNReal.ofReal 2) (μ.restrict S) := by
    rw [← integrable_norm_rpow_iff hg (by simp) ENNReal.ofReal_ne_top]
    refine hg2.congr (ae_of_all _ fun x => ?_)
    simp only [ENNReal.toReal_ofReal zero_le_two, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  -- Hölder with `p = q = 2` for `g` and the constant `1 ∈ L²(ν)`.
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (f := g) (g := fun _ => (1 : ℝ))
    Real.HolderConjugate.two_two (hgD.mono fun x hx => hx.1) (ae_of_all _ fun _ => zero_le_one)
    hgL2 (memLp_const 1)
  simp only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul, measureReal_def,
    Measure.restrict_apply_univ, ← Real.sqrt_eq_rpow] at hH
  -- `∫_S g² ≤ ∫_S D`, and `√` is monotone.
  have hmono : ∫ x in S, g x ^ 2 ∂μ ≤ ∫ x in S, D x ∂μ :=
    integral_mono_ae hg2 hD (hgD.mono fun x hx => hx.2)
  calc ∫ x in S, g x ∂μ ≤ Real.sqrt (∫ x in S, g x ^ 2 ∂μ) * Real.sqrt (μ S).toReal := hH
    _ ≤ Real.sqrt (∫ x in S, D x ∂μ) * Real.sqrt (μ S).toReal :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmono) (Real.sqrt_nonneg _)
    _ = Real.sqrt (μ S).toReal * Real.sqrt (∫ x in S, D x ∂μ) := mul_comm _ _
/-- Simon 4.5 (15): the error made by dropping the weight `W` in the weak equation
(steps 4-6 of `gwe_weighted_energy_weak_equation`). -/
theorem gwe_wewe_weight_error_bound : ∀ (n ℓ : ℕ) (cJ σ κ M : ℝ) (f : Rn n → Rn ℓ) (W ζ : Rn n → ℝ) (j : Fin ℓ), 0 ≤ cJ → 0 < σ → 0 ≤ κ → κ ≤ 1 → LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → Measurable W → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨ (1 ≤ W x ∧ W x ≤ (1 + κ) * (1 + cJ * hsNormSq (fderiv ℝ f x)))) → (∀ x, ‖gradient ζ x‖ ≤ M) → |(∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)) - ∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x| ≤ M * (volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0})).toReal + M * κ * (∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖) + 2 * cJ * M * ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x) := by
  intro n ℓ cJ σ κ M f W ζ j hcJ hσ hκ0 hκ1 hf hW hH1 hζ
  -- Sibling `lipschitz_fderiv_facts` with `r = σ / 2`.
  obtain ⟨hDm, hGm, hD0, hbd, -⟩ := Submission.gwe_wewe_lipschitz_fderiv_facts n ℓ (σ / 2) f hf
  -- `B₂ = ball 0 (σ/4) ⊆ B₁ = ball 0 (3σ/8) ⊆ ball 0 (σ/2)`.
  have hB21 : ball (0 : Rn n) (σ / 4) ⊆ ball 0 (3 * σ / 8) := ball_subset_ball (by linarith)
  have hB1h : ball (0 : Rn n) (3 * σ / 8) ⊆ ball 0 (σ / 2) := ball_subset_ball (by linarith)
  have hB2fin : volume (ball (0 : Rn n) (σ / 4)) ≠ ∞ := measure_ball_lt_top.ne
  have hM : 0 ≤ M := (norm_nonneg _).trans (hζ 0)
  -- Measurability of `∇ζ = (toDual)⁻¹ ∘ Dζ` and of `u = ⟨∇f^j, ∇ζ⟩`.
  have hζm : Measurable (gradient ζ) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ ζ)
  have hum : Measurable fun x => inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) :=
    continuous_inner.measurable.comp ((hGm j).prodMk hζm)
  -- `|u| ≤ M ‖∇f^j‖` (Cauchy–Schwarz).
  have hu_le : ∀ x, |inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤
      M * ‖gradient (fun y => f y j) x‖ := fun x =>
    (abs_real_inner_le_norm _ _).trans <| by
      rw [mul_comm M]; exact mul_le_mul_of_nonneg_left (hζ x) (norm_nonneg _)
  -- Integrability on `B₂` of `u`, `‖∇f^j‖`, `|Df|²` and `M 𝟙_N`, `N = B₁ ∩ {W = 0}`.
  have hu_int : IntegrableOn (fun x => inner ℝ (gradient (fun y => f y j) x) (gradient ζ x))
      (ball (0 : Rn n) (σ / 4)) := by
    refine Measure.integrableOn_of_bounded (M := M) hB2fin hum.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [Real.norm_eq_abs]
    exact (hu_le x).trans (mul_le_of_le_one_right hM ((hbd x (hB1h (hB21 hx))).2 j))
  have hG_int : IntegrableOn (fun x => ‖gradient (fun y => f y j) x‖)
      (ball (0 : Rn n) (σ / 4)) := by
    refine Measure.integrableOn_of_bounded (M := 1) hB2fin (hGm j).norm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [norm_norm]
    exact (hbd x (hB1h (hB21 hx))).2 j
  have hD_int : IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) (ball (0 : Rn n) (σ / 4)) := by
    refine Measure.integrableOn_of_bounded (M := n) hB2fin hDm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hD0 x)]
    exact (hbd x (hB1h (hB21 hx))).1
  have hN : MeasurableSet (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) :=
    measurableSet_ball.inter (measurableSet_eq_fun hW measurable_const)
  have hI_int : IntegrableOn ((ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator fun _ => M)
      (ball (0 : Rn n) (σ / 4)) :=
    (integrableOn_const hB2fin).indicator hN
  have hIG_int : IntegrableOn (fun x => (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator
      (fun _ => M) x + M * κ * ‖gradient (fun y => f y j) x‖) (ball (0 : Rn n) (σ / 4)) :=
    hI_int.add (hG_int.const_mul (M * κ))
  have hh_int : IntegrableOn (fun x => (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator
      (fun _ => M) x + M * κ * ‖gradient (fun y => f y j) x‖ + 2 * cJ * M * hsNormSq (fderiv ℝ f x))
      (ball (0 : Rn n) (σ / 4)) :=
    hIG_int.add (hD_int.const_mul (2 * cJ * M))
  -- Pointwise error: `|u - uW| ≤ M 𝟙_N + M κ ‖∇f^j‖ + 2 cJ M |Df|²` a.e. on `B₂`.
  have hpt : ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) (σ / 4))),
      ‖inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) -
          inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x‖ ≤
        (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator (fun _ => M) x +
          M * κ * ‖gradient (fun y => f y j) x‖ + 2 * cJ * M * hsNormSq (fderiv ℝ f x) := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hH1] with x hx hHx
    have hx1 : x ∈ ball (0 : Rn n) (3 * σ / 8) := hB21 hx
    have hG1 : ‖gradient (fun y => f y j) x‖ ≤ 1 := (hbd x (hB1h hx1)).2 j
    have hG0 : 0 ≤ ‖gradient (fun y => f y j) x‖ := norm_nonneg _
    have hDx : 0 ≤ hsNormSq (fderiv ℝ f x) := hD0 x
    have hux := hu_le x
    have hκG : 0 ≤ M * κ * ‖gradient (fun y => f y j) x‖ := by positivity
    have hcD : 0 ≤ 2 * cJ * M * hsNormSq (fderiv ℝ f x) := by positivity
    rw [Real.norm_eq_abs]
    rcases hHx hx1 with h0 | ⟨h1, h2⟩
    · -- `W x = 0`: then `x ∈ N` and `|u - uW| = |u| ≤ M`.
      rw [indicator_of_mem (show x ∈ ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0} from ⟨hx1, h0⟩),
        h0, mul_zero, sub_zero]
      have hMG : M * ‖gradient (fun y => f y j) x‖ ≤ M := mul_le_of_le_one_right hM hG1
      linarith
    · -- `1 ≤ W x ≤ (1 + κ)(1 + cJ |Df|²)`: then `x ∉ N` and `|u - uW| = |u| (W - 1)`.
      rw [indicator_of_notMem (fun h : x ∈ ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0} => by
        have h' : W x = 0 := h.2
        linarith), zero_add]
      have hw1 : 0 ≤ W x - 1 := by linarith
      have hwκ : W x - 1 ≤ κ + 2 * cJ * hsNormSq (fderiv ℝ f x) := by
        nlinarith [mul_le_mul_of_nonneg_right (show 1 + κ ≤ 2 by linarith) (mul_nonneg hcJ hDx)]
      rw [show inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) -
            inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x =
          -(inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * (W x - 1)) by ring,
        abs_neg, abs_mul, abs_of_nonneg hw1]
      calc |inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| * (W x - 1)
          ≤ M * ‖gradient (fun y => f y j) x‖ * (κ + 2 * cJ * hsNormSq (fderiv ℝ f x)) :=
            mul_le_mul hux hwκ hw1 (mul_nonneg hM hG0)
        _ = M * κ * ‖gradient (fun y => f y j) x‖ +
              2 * cJ * M * hsNormSq (fderiv ℝ f x) * ‖gradient (fun y => f y j) x‖ := by ring
        _ ≤ M * κ * ‖gradient (fun y => f y j) x‖ + 2 * cJ * M * hsNormSq (fderiv ℝ f x) := by
            linarith [mul_le_of_le_one_right hcD hG1]
  -- `uW = u - (u - uW)` is integrable on `B₂`.
  have hdiff_int : IntegrableOn (fun x => inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) -
      inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x) (ball (0 : Rn n) (σ / 4)) :=
    Integrable.mono' hh_int (hum.sub (hum.mul hW)).aestronglyMeasurable hpt
  have huW_int : IntegrableOn (fun x => inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x)
      (ball (0 : Rn n) (σ / 4)) := by
    refine (hu_int.sub hdiff_int).congr ?_
    filter_upwards with x
    simp
  -- The indicator term: `∫_{B₂} M 𝟙_N = M Lⁿ(N ∩ B₂) ≤ M Lⁿ(N)`.
  have hNfin : volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have hI : ∫ x in ball (0 : Rn n) (σ / 4),
      (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator (fun _ => M) x ≤
      M * (volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0})).toReal := by
    rw [integral_indicator_const M hN, measureReal_restrict_apply hN, smul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (measureReal_mono inter_subset_left hNfin) hM
  -- Integrate the pointwise error.
  calc |(∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)) -
        ∫ x in ball (0 : Rn n) (σ / 4),
          inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x|
      = ‖∫ x in ball (0 : Rn n) (σ / 4), (inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) -
          inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x)‖ := by
        rw [integral_sub hu_int huW_int, Real.norm_eq_abs]
    _ ≤ ∫ x in ball (0 : Rn n) (σ / 4), ((ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator
          (fun _ => M) x + M * κ * ‖gradient (fun y => f y j) x‖ +
          2 * cJ * M * hsNormSq (fderiv ℝ f x)) :=
        norm_integral_le_of_norm_le hh_int hpt
    _ = (∫ x in ball (0 : Rn n) (σ / 4),
          (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}).indicator (fun _ => M) x) +
          M * κ * (∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖) +
          2 * cJ * M * ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x) := by
        rw [integral_add hIG_int (hD_int.const_mul (2 * cJ * M)),
          integral_add hI_int (hG_int.const_mul (M * κ)), integral_const_mul, integral_const_mul]
    _ ≤ M * (volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0})).toReal +
          M * κ * (∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖) +
          2 * cJ * M * ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x) := by
        linarith
/-- Simon Ch. 5, 4.5 (14)–(16) in the parameter domain: from the weighted estimates
`Lⁿ(B̆_{3σ/8} ∩ {W = 0}) ≤ K₀Eσⁿ` and `∫_{B̆_{3σ/8}} |Df|² W ≤ K₀Eσⁿ` to the unweighted energy
bound `∫_{B̆_{3σ/8}} |Df|² ≤ CEσⁿ` and the approximate weak equation
`|∫_{B̆_{σ/4}} ⟨∇fʲ, ∇ζ⟩| ≤ C(E + h + κ√E)Mσⁿ`.  The constant is
`C = max {C_E, 2K₀ + 2c_J C_E, √(ω C_E), 1}` with `C_E = (1 + n)K₀` and `ω = Lⁿ(B̆₁(0))`. -/
theorem gwe_weighted_energy_weak_equation : ∀ n ℓ : ℕ, 1 ≤ n → ∀ K0 cJ : ℝ, 0 ≤ K0 → 0 ≤ cJ → ∃ C : ℝ, 0 < C ∧ ∀ (σ κ E h : ℝ) (f : Rn n → Rn ℓ) (W : Rn n → ℝ), 0 < σ → 0 ≤ κ → κ ≤ 1 → 0 ≤ E → 0 ≤ h → LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → Measurable W → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨ (1 ≤ W x ∧ W x ≤ (1 + κ) * (1 + cJ * hsNormSq (fderiv ℝ f x)))) → volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → ∫⁻ x in ball (0 : Rn n) (3 * σ / 8), ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → (∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x) ≤ C * E * σ ^ n) ∧ ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x| ≤ K0 * (E + h) * M * σ ^ n → |∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤ C * (E + h + κ * Real.sqrt E) * M * σ ^ n := by
  intro n ℓ _ K0 cJ hK0 hcJ
  -- The constants depend only on `n`, `K0` and `cJ`.
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = (volume (ball (0 : Rn n) 1)).toReal := ⟨_, rfl⟩
  obtain ⟨CE, hCE⟩ : ∃ CE : ℝ, CE = (1 + n) * K0 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = max (max CE (2 * K0 + 2 * cJ * CE)) (max (Real.sqrt (ω * CE)) 1) := ⟨_, rfl⟩
  have hω0 : 0 ≤ ω := by rw [hω]; exact ENNReal.toReal_nonneg
  have hCE0 : 0 ≤ CE := by rw [hCE]; positivity
  have hCEC : CE ≤ C := by rw [hC]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hKC : 2 * K0 + 2 * cJ * CE ≤ C := by
    rw [hC]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hsqC : Real.sqrt (ω * CE) ≤ C := by
    rw [hC]; exact (le_max_left _ _).trans (le_max_right _ _)
  have h1C : 1 ≤ C := by rw [hC]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hK0C : K0 ≤ C := by linarith [mul_nonneg hcJ hCE0]
  refine ⟨C, one_pos.trans_le h1C, ?_⟩
  intro σ κ E h f W hσ hκ0 hκ1 hE hh hf hW hH1 hH2 hH3
  have hσn : 0 ≤ σ ^ n := pow_nonneg hσ.le n
  have hKE : 0 ≤ K0 * E * σ ^ n := by positivity
  -- Step 1: derivative facts on `B̆_{σ/2}(0)`.
  obtain ⟨-, hGmeas, hDnn, -, hae⟩ := Submission.gwe_wewe_lipschitz_fderiv_facts n ℓ (σ / 2) f hf
  -- Steps 2–3: the unweighted energy bound, with constant `C_E = (1 + n) K0`.
  have hH1' : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨ 1 ≤ W x := by
    filter_upwards [hH1] with x hx hxB
    exact (hx hxB).imp id And.left
  obtain ⟨hDint, hEnergy⟩ :=
    Submission.gwe_wewe_energy_bound n ℓ K0 σ E f W hK0 hσ hE hf hW hH1' hH2 hH3
  refine ⟨?_, ?_⟩
  · calc ∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x)
        ≤ (1 + n) * K0 * E * σ ^ n := hEnergy
      _ = CE * (E * σ ^ n) := by rw [hCE]; ring
      _ ≤ C * (E * σ ^ n) := mul_le_mul_of_nonneg_right hCEC (mul_nonneg hE hσn)
      _ = C * E * σ ^ n := by ring
  -- Steps 4–7: the weak equation.
  intro ζ _ _ _ M hM j hWeq
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have herr := Submission.gwe_wewe_weight_error_bound n ℓ cJ σ κ M f W ζ j hcJ hσ hκ0 hκ1 hf hW
    hH1 hM
  have hN : (volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0})).toReal ≤ K0 * E * σ ^ n :=
    ENNReal.toReal_le_of_le_ofReal hKE hH2
  have hB21 : ball (0 : Rn n) (σ / 4) ⊆ ball 0 (3 * σ / 8) := ball_subset_ball (by linarith)
  have hB2 : ball (0 : Rn n) (σ / 4) ⊆ ball 0 (σ / 2) := ball_subset_ball (by linarith)
  have hD2 : ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x) ≤ CE * E * σ ^ n :=
    calc ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x)
        ≤ ∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x) :=
          setIntegral_mono_set hDint (ae_of_all _ hDnn) hB21.eventuallyLE
      _ ≤ (1 + n) * K0 * E * σ ^ n := hEnergy
      _ = CE * E * σ ^ n := by rw [hCE]
  -- Cauchy–Schwarz on `B̆_{σ/4}(0)`, with `‖∇fʲ‖² ≤ |Df|²` a.e.
  have hG : ∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖ ≤
      Real.sqrt (volume (ball (0 : Rn n) (σ / 4))).toReal *
        Real.sqrt (∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x)) := by
    refine Submission.gwe_wewe_setIntegral_le_sqrt_mul_sqrt (Rn n) volume (ball 0 (σ / 4))
      (fun x => ‖gradient (fun y => f y j) x‖) (fun x => hsNormSq (fderiv ℝ f x))
      measure_ball_lt_top (hGmeas j).norm.aestronglyMeasurable (hDint.mono_set hB21) ?_
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hae] with x hx hxB
    exact ⟨norm_nonneg _, hx (hB2 hxB) j⟩
  have hvol : (volume (ball (0 : Rn n) (σ / 4))).toReal ≤ ω * σ ^ n := by
    have hσ4 : (0 : ℝ) < σ / 4 := by positivity
    rw [Measure.addHaar_ball_of_pos volume (0 : Rn n) hσ4, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hσ4.le n), ← hω, mul_comm ω]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσ4.le (by linarith) n) hω0
  have hGb : ∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖ ≤
      Real.sqrt (ω * CE) * σ ^ n * Real.sqrt E :=
    calc ∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖
        ≤ Real.sqrt (volume (ball (0 : Rn n) (σ / 4))).toReal *
            Real.sqrt (∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x)) := hG
      _ ≤ Real.sqrt (ω * σ ^ n) * Real.sqrt (CE * E * σ ^ n) :=
          mul_le_mul (Real.sqrt_le_sqrt hvol) (Real.sqrt_le_sqrt hD2) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = Real.sqrt (ω * CE) * σ ^ n * Real.sqrt E := by
          rw [← Real.sqrt_mul (mul_nonneg hω0 hσn),
            show ω * σ ^ n * (CE * E * σ ^ n) = (σ ^ n) ^ 2 * (ω * CE * E) by ring,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hσn, Real.sqrt_mul (mul_nonneg hω0 hCE0)]
          ring
  -- Collect the terms.
  have h1 := mul_le_mul_of_nonneg_left hN hM0
  have h2 := mul_le_mul_of_nonneg_left hGb (mul_nonneg hM0 hκ0)
  have h3 := mul_le_mul_of_nonneg_left hD2 (mul_nonneg (mul_nonneg zero_le_two hcJ) hM0)
  have hfinal : K0 * (E + h) * M * σ ^ n + (M * (K0 * E * σ ^ n) +
      M * κ * (Real.sqrt (ω * CE) * σ ^ n * Real.sqrt E) + 2 * cJ * M * (CE * E * σ ^ n)) ≤
      C * (E + h + κ * Real.sqrt E) * M * σ ^ n := by
    have e1 := mul_le_mul_of_nonneg_right hKC hE
    have e2 := mul_le_mul_of_nonneg_right hK0C hh
    have e3 := mul_le_mul_of_nonneg_right hsqC (mul_nonneg hκ0 (Real.sqrt_nonneg E))
    calc K0 * (E + h) * M * σ ^ n + (M * (K0 * E * σ ^ n) +
          M * κ * (Real.sqrt (ω * CE) * σ ^ n * Real.sqrt E) + 2 * cJ * M * (CE * E * σ ^ n))
        = ((2 * K0 + 2 * cJ * CE) * E + K0 * h + Real.sqrt (ω * CE) * (κ * Real.sqrt E)) *
            (M * σ ^ n) := by ring
      _ ≤ C * (E + h + κ * Real.sqrt E) * (M * σ ^ n) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hM0 hσn)
      _ = C * (E + h + κ * Real.sqrt E) * M * σ ^ n := by ring
  have key := abs_sub_abs_le_abs_sub
    (∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x))
    (∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x)
  linarith
/-- Simon Ch. 5, proof of Theorem 4.5 (pp. 117–119), displays (6)–(16), for a `1`-Lipschitz graph
approximation `f` of `V` over `Bⁿ_{σ/2}`: the energy bound `∫_{B̆ⁿ_{3σ/8}} |Df|² ≤ C E σⁿ` and the
approximate weak equation `|∫_{B̆ⁿ_{σ/4}} ∇f^j · ∇ζ| ≤ C (E + h + κ √E) M σⁿ`, `C = C(n, ℓ, K_b)`.
For the graph map `F(x') = q(x', f(x'))` and `A ⊆ Bⁿ_{σ/2}`, `μ_V ⌞ F(A)` is the image under `F` of
`W Lⁿ ⌞ A`, where `W = J_F θ(F)` a.e. (`gwe_varifold_graph_transfer`). Where `W ≠ 0`,
`1 ≤ W ≤ (1 + κ)(1 + c_n |Df|²)` with `c_n = e^{n/2}/2` (`gwe_graph_jacobian_bounds`). Up to a
null set, `F` maps `{W = 0} ∩ B̆ⁿ_{3σ/8}` into `(Γ \ spt V) ∪ (spt V \ M)`, `Γ = F(Bⁿ_{σ/2})`; since
`J_F ≥ 1`, the area formula (`gwe_lipschitz_graph_area_formula`) gives
`Lⁿ({W = 0} ∩ B̆ⁿ_{3σ/8}) ≤ K_b E σⁿ`. On the graph, `p_{T_x M}` projects onto the tangent plane
of `F`, so (13) (`gwe_graph_tilt_algebra`) gives `∫_{B̆ⁿ_{3σ/8}} |Df|² W ≤ (ℓ + ½) E σⁿ`. The
weighted weak equation (12) is `gwe_graph_tangential_estimate`, with error at most
`(K_b E + E + h/4) M σⁿ`. Finally `gwe_weighted_energy_weak_equation` with `K₀ = K_b + ℓ + 1`
removes the weight `W` ((14)–(16)). -/
theorem ted_graph_weak_equation : ∀ n ℓ : ℕ, 1 ≤ n → ∀ Kb : ℝ, 0 ≤ Kb → ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → ∀ σ : ℝ, 0 < σ → closedBall 0 σ ⊆ U → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ), LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → (∀ x ∈ closedBall (0 : Rn n) (σ / 2), ‖f x‖ ≤ σ / 16) → (∀ x ∈ V.support ∩ closedBall 0 σ, infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ σ / 16) → (∀ᵐ x ∂V.weight, ∀ x' ∈ ball (0 : Rn n) (σ / 2), x = q (graphPoint x' (f x')) → DifferentiableAt ℝ f x' → V.tangentProj x = (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (fderiv ℝ f x' v)))).starProjection) → ∀ κ E h : ℝ, 0 ≤ κ → κ ≤ 1 → 0 ≤ E → 0 ≤ h → (∀ᵐ x ∂V.weight, x ∈ closedBall 0 σ → 1 ≤ V.mult x ∧ V.mult x ≤ 1 + κ) → (μHE[n] : Measure (Amb n ℓ)) ((V.support ∩ closedBall 0 σ) \ V.carrier) = 0 → ∫ x in closedBall 0 σ, hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight ≤ E * σ ^ n → V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) + (μHE[n] : Measure (Amb n ℓ)) (closedBall 0 (σ / 2) ∩ (q '' graphOver f (closedBall 0 (σ / 2)) \ V.support)) ≤ ENNReal.ofReal (Kb * E * σ ^ n) → ∫ x in closedBall 0 (σ / 2), ‖H x‖ ∂V.weight ≤ h * σ ^ (n - 1) → (∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x) ≤ C * E * σ ^ n) ∧ ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤ C * (E + h + κ * Real.sqrt E) * M * σ ^ n := by
  intro n ℓ hn Kb hKb
  obtain ⟨C, hC, hmain⟩ := Submission.gwe_weighted_energy_weak_equation n ℓ hn (Kb + ℓ + 1)
    (Real.exp ((n : ℝ) / 2) / 2) (by positivity) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro U hU V H hH hmeas σ hσ hσU q f hf hfb hheight htan κ E h hκ0 hκ1 hE hh hmult hcar htilt
    hbad hHint
  -- `W`: the density of the pull-back of `μ_V ⌞ F(Bⁿ_{σ/2})` under `F`, `W = J_F θ(F)` a.e.
  obtain ⟨W, hWm, -, hWl, hWi, hWae, hWnull⟩ :=
    Submission.gwe_varifold_graph_transfer n ℓ hn U V q f (σ / 2) hf
  have hEσ : 0 ≤ E * σ ^ n := mul_nonneg hE (pow_nonneg hσ.le n)
  have hhs : ∀ D : Rn n →L[ℝ] Rn ℓ, 0 ≤ hsNormSq D := fun D =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hball : ∀ x ∈ ball (0 : Rn n) (3 * σ / 8), x ∈ ball (0 : Rn n) (σ / 2) := fun x hx =>
    ball_subset_ball (by linarith) hx
  -- graph coordinates: with `q⁻¹ x = (a(x), b(x))`, `a(q(x', y)) = x'`, so `a(F(x')) = x'`
  have hfst := (Submission.gte_graph_image_geometry n ℓ q).2.2.1
  -- `∇g(a(x)) · ∇ζ(a(x))` is Borel: gradients are measurable (`measurable_fderiv`, then the Riesz
  -- isometry `(toDual ℝ ℝⁿ)⁻¹`) and `a` is continuous
  have hmeasg : ∀ g ζ : Rn n → ℝ, Measurable fun x : Amb n ℓ =>
      inner ℝ (gradient g (EuclideanSpace.finAddEquivProd (q.symm x)).1)
        (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) := by
    intro g ζ
    have hgrad : ∀ u : Rn n → ℝ, Measurable (gradient u) := fun u => by
      have e : gradient u = fun x => (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ u x) := rfl
      rw [e]
      exact (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp
        (measurable_fderiv ℝ u)
    have ha : Measurable fun x : Amb n ℓ => (EuclideanSpace.finAddEquivProd (q.symm x)).1 :=
      (continuous_fst.comp
        (EuclideanSpace.finAddEquivProd.continuous.comp q.symm.continuous)).measurable
    exact continuous_inner.measurable2 ((hgrad g).comp ha) ((hgrad ζ).comp ha)
  -- `‖Df‖ ≤ 1` on `B̆ⁿ_{σ/2}`, a neighbourhood of each of its points on which `f` is `1`-Lipschitz
  have hDf : ∀ x ∈ ball (0 : Rn n) (σ / 2), ‖fderiv ℝ f x‖ ≤ 1 := fun x hx => by
    simpa using norm_fderiv_le_of_lipschitzOn ℝ
      (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) hf
  -- `|F(x')|² = |x'|² + |f(x')|² ≤ (3σ/8)² + (σ/16)² < (σ/2)²` for `x' ∈ B̆ⁿ_{3σ/8}`
  have hF : ∀ x ∈ ball (0 : Rn n) (3 * σ / 8),
      q (graphPoint x (f x)) ∈ closedBall (0 : Amb n ℓ) (σ / 2) := by
    intro x hx
    have hx' : ‖x‖ < 3 * σ / 8 := mem_ball_zero_iff.mp hx
    have hfx : ‖f x‖ ≤ σ / 16 := hfb x (mem_closedBall_zero_iff.mpr (by linarith))
    have h1 : ‖x‖ ^ 2 ≤ (3 * σ / 8) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx'.le 2
    have h2 : ‖f x‖ ^ 2 ≤ (σ / 16) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hfx 2
    have h3 : ‖graphPoint x (f x)‖ ^ 2 ≤ (σ / 2) ^ 2 := by
      rw [(Submission.lip_approx_graph_coordinates n ℓ q).2.1 x (f x)]
      nlinarith
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    nlinarith [norm_nonneg (graphPoint x (f x))]
  have hFσ : ∀ x ∈ ball (0 : Rn n) (3 * σ / 8),
      q (graphPoint x (f x)) ∈ closedBall (0 : Amb n ℓ) σ :=
    fun x hx => closedBall_subset_closedBall (by linarith) (hF x hx)
  -- (i) Where `W ≠ 0`: `F(x') ∈ M`, `1 ≤ θ(F(x')) ≤ 1 + κ` (off the preimage of a `μ_V`-null set),
  -- and `1 ≤ J_F ≤ 1 + c_n |Df|²`, so `1 ≤ W = J_F θ(F) ≤ (1 + κ)(1 + c_n |Df|²)`.
  have hZ : V.weight
      {y | ¬(y ∈ closedBall (0 : Amb n ℓ) σ → 1 ≤ V.mult y ∧ V.mult y ≤ 1 + κ)} = 0 :=
    ae_iff.mp hmult
  have hW1 : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨
      (1 ≤ W x ∧ W x ≤ (1 + κ) * (1 + Real.exp ((n : ℝ) / 2) / 2 * hsNormSq (fderiv ℝ f x))) := by
    filter_upwards [hWae, hWnull _ hZ] with x hxW hxZ hx
    by_cases hW : W x = 0
    · exact Or.inl hW
    refine Or.inr ?_
    have hθ : 1 ≤ V.mult (q (graphPoint x (f x))) ∧ V.mult (q (graphPoint x (f x))) ≤ 1 + κ := by
      by_contra hcon
      exact hW (hxZ (ball_subset_closedBall (hball x hx)) fun h' => hcon (h' (hFσ x hx)))
    have hJ := Submission.gwe_graph_jacobian_bounds n ℓ (fderiv ℝ f x)
    have hJ2 := hJ.2 (hDf x (hball x hx))
    rw [hxW (hball x hx)] at hW ⊢
    by_cases hM : q (graphPoint x (f x)) ∈ V.carrier
    · rw [indicator_of_mem hM]
      refine ⟨by nlinarith [hJ.1, hθ.1], ?_⟩
      rw [mul_comm (1 + κ)]
      exact mul_le_mul hJ2 hθ.2 (by linarith [hθ.1]) (by linarith [hJ.1])
    · rw [indicator_of_notMem hM, mul_zero] at hW
      exact absurd rfl hW
  -- (ii) (4): up to a null set, `F` maps `{W = 0} ∩ B̆ⁿ_{3σ/8}` into
  -- `(B_{σ/2} ∩ (Γ \ spt V)) ∪ ((spt V ∩ B_σ) \ M)`; as `J_F ≥ 1`, the area formula gives
  -- `Lⁿ({W = 0} ∩ B̆ⁿ_{3σ/8}) ≤ Hⁿ(F({W = 0} ∩ B̆ⁿ_{3σ/8})) ≤ K_b E σⁿ + 0`.
  have hW2 : volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) ≤
      ENNReal.ofReal ((Kb + ℓ + 1) * E * σ ^ n) := by
    obtain ⟨G, hGsub, hGm, hG0⟩ := exists_measurable_superset_of_null (ae_iff.mp hWae)
    have hSm : MeasurableSet ((ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) \ G) :=
      (measurableSet_ball.inter (hWm (measurableSet_singleton 0))).diff hGm
    have hSsub : (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) \ G ⊆ closedBall 0 (σ / 2) :=
      fun x hx => ball_subset_closedBall (hball x hx.1.1)
    have himage : q '' graphOver f ((ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) \ G) ⊆
        closedBall 0 (σ / 2) ∩ (q '' graphOver f (closedBall 0 (σ / 2)) \ V.support) ∪
          (V.support ∩ closedBall 0 σ) \ V.carrier := by
      rintro _ ⟨_, ⟨x, ⟨⟨hx, hWx⟩, hxG⟩, rfl⟩, rfl⟩
      have hWx' : W x = 0 := hWx
      have hP := fun hc => hxG (hGsub hc)
      simp only [mem_ofPred_eq, imp_false, not_not] at hP
      have hJ1 := (Submission.gwe_graph_jacobian_bounds n ℓ (fderiv ℝ f x)).1
      have hnot : q (graphPoint x (f x)) ∉ V.carrier := by
        intro hM
        have hpos := V.mult_pos _ hM
        have h0 := hP (hball x hx)
        rw [hWx', indicator_of_mem hM] at h0
        nlinarith
      by_cases hs : q (graphPoint x (f x)) ∈ V.support
      · exact Or.inr ⟨⟨hs, hFσ x hx⟩, hnot⟩
      · exact Or.inl ⟨hF x hx, ⟨_, ⟨x, ball_subset_closedBall (hball x hx), rfl⟩, rfl⟩, hs⟩
    calc volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0})
        = volume ((ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) \ G) :=
          (measure_sdiff_null hG0).symm
      _ = ∫⁻ _ in (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) \ G, (1 : ℝ≥0∞) :=
          (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) \ G,
            ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
              Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ)))
                (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ)))))) * 1 := by
          refine lintegral_mono fun x => ?_
          rw [mul_one]
          exact ENNReal.one_le_ofReal.mpr
            (Submission.gwe_graph_jacobian_bounds n ℓ (fderiv ℝ f x)).1
      _ = ∫⁻ _ in q '' graphOver f ((ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) \ G), (1 : ℝ≥0∞)
            ∂(μHE[n] : Measure (Amb n ℓ)) :=
          (Submission.gwe_lipschitz_graph_area_formula n ℓ hn q f 1 (σ / 2) hf _ hSm hSsub
            fun _ => 1).symm
      _ = (μHE[n] : Measure (Amb n ℓ))
            (q '' graphOver f ((ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) \ G)) :=
          setLIntegral_one _
      _ ≤ (μHE[n] : Measure (Amb n ℓ))
            (closedBall 0 (σ / 2) ∩ (q '' graphOver f (closedBall 0 (σ / 2)) \ V.support) ∪
              (V.support ∩ closedBall 0 σ) \ V.carrier) := measure_mono himage
      _ ≤ (μHE[n] : Measure (Amb n ℓ))
            (closedBall 0 (σ / 2) ∩ (q '' graphOver f (closedBall 0 (σ / 2)) \ V.support)) +
          (μHE[n] : Measure (Amb n ℓ)) ((V.support ∩ closedBall 0 σ) \ V.carrier) :=
          measure_union_le _ _
      _ ≤ V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) +
          (μHE[n] : Measure (Amb n ℓ))
            (closedBall 0 (σ / 2) ∩ (q '' graphOver f (closedBall 0 (σ / 2)) \ V.support)) := by
          rw [hcar, add_zero]
          exact le_add_self
      _ ≤ ENNReal.ofReal (Kb * E * σ ^ n) := hbad
      _ ≤ ENNReal.ofReal ((Kb + ℓ + 1) * E * σ ^ n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [mul_nonneg (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ) hEσ]
  -- (iii) (13), (14): on the graph, `|Df(a(x))|² ≤ (ℓ + ½) |p_{T_x M} − p_T|²` `μ_V`-a.e.
  -- (`p_{T_x M}` is the projection onto the tangent plane of `F`), so after transferring by `F`,
  -- `∫_{B̆ⁿ_{3σ/8}} |Df|² W ≤ (ℓ + ½) ∫_{B_σ} |p_{T_x M} − p_T|² dμ_V ≤ (ℓ + ½) E σⁿ`.
  have hW3 : ∫⁻ x in ball (0 : Rn n) (3 * σ / 8), ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x) ≤
      ENNReal.ofReal ((Kb + ℓ + 1) * E * σ ^ n) := by
    -- `|p_{T_x M} − p_T|²` is `μ_V`-integrable on the compact `B_σ(0) ⊆ U`, of finite weight
    have hint : IntegrableOn
        (fun x => hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection))
        (closedBall 0 σ) V.weight :=
      ((Submission.gte_tangentProj_integrands n ℓ U V).2 hmeas _
        ((Submission.gte_weight_null_finite n ℓ U V).1 _ (isCompact_closedBall 0 σ) hσU)).2 _
    -- `φ = |Df(a(·))|²` on the graph `F(B̆ⁿ_{σ/2})` and `0` elsewhere, so `φ ∘ F = |Df|²` there
    obtain ⟨φ, hφ⟩ : ∃ φ : Amb n ℓ → ℝ≥0∞, φ = (q '' graphOver f (ball 0 (σ / 2))).indicator
        fun y => ENNReal.ofReal
          (hsNormSq (fderiv ℝ f (EuclideanSpace.finAddEquivProd (q.symm y)).1)) :=
      ⟨_, rfl⟩
    have hφF : ∀ x ∈ ball (0 : Rn n) (σ / 2),
        φ (q (graphPoint x (f x))) = ENNReal.ofReal (hsNormSq (fderiv ℝ f x)) := by
      intro x hx
      have hmem : q (graphPoint x (f x)) ∈ q '' graphOver f (ball 0 (σ / 2)) :=
        ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [hφ, indicator_of_mem hmem, hfst]
    have hφle : ∀ᵐ y ∂V.weight, φ y ≤ ENNReal.ofReal (((ℓ : ℝ) + 1 / 2) *
        hsNormSq (V.tangentProj y - (rotatedPlane q).starProjection)) := by
      filter_upwards [htan] with y hy
      by_cases hyG : y ∈ q '' graphOver f (ball 0 (σ / 2))
      · obtain ⟨_, ⟨x', hx', rfl⟩, rfl⟩ := hyG
        rw [hφF x' hx']
        refine ENNReal.ofReal_le_ofReal ?_
        by_cases hd : DifferentiableAt ℝ f x'
        · rw [hy x' hx' rfl hd]
          exact (Submission.gwe_graph_tilt_algebra n ℓ q (fderiv ℝ f x') (hDf x' hx')).1
        · rw [fderiv_zero_of_not_differentiableAt hd]
          have h0 : hsNormSq (0 : Rn n →L[ℝ] Rn ℓ) = 0 := by simp [hsNormSq]
          rw [h0]
          exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      · rw [hφ, indicator_of_notMem hyG]
        exact zero_le
    have hsub : q '' graphOver f (ball 0 (3 * σ / 8)) ⊆ closedBall (0 : Amb n ℓ) σ := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact hFσ x hx
    calc ∫⁻ x in ball (0 : Rn n) (3 * σ / 8), ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x)
        = ∫⁻ x in ball (0 : Rn n) (3 * σ / 8),
            ENNReal.ofReal (W x) * φ (q (graphPoint x (f x))) := by
          refine setLIntegral_congr_fun measurableSet_ball fun x hx => ?_
          rw [hφF x (hball x hx), ENNReal.ofReal_mul (hhs _), mul_comm]
      _ = ∫⁻ y in q '' graphOver f (ball 0 (3 * σ / 8)), φ y ∂V.weight :=
          (hWl _ measurableSet_ball
            (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) φ).symm
      _ ≤ ∫⁻ y in q '' graphOver f (ball 0 (3 * σ / 8)), ENNReal.ofReal (((ℓ : ℝ) + 1 / 2) *
            hsNormSq (V.tangentProj y - (rotatedPlane q).starProjection)) ∂V.weight :=
          lintegral_mono_ae (ae_restrict_of_ae hφle)
      _ ≤ ∫⁻ y in closedBall 0 σ, ENNReal.ofReal (((ℓ : ℝ) + 1 / 2) *
            hsNormSq (V.tangentProj y - (rotatedPlane q).starProjection)) ∂V.weight :=
          lintegral_mono_set hsub
      _ = ENNReal.ofReal (∫ y in closedBall 0 σ, ((ℓ : ℝ) + 1 / 2) *
            hsNormSq (V.tangentProj y - (rotatedPlane q).starProjection) ∂V.weight) :=
          (ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) (ae_of_all _ fun y =>
            mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _))).symm
      _ ≤ ENNReal.ofReal ((Kb + ℓ + 1) * E * σ ^ n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_const_mul]
          have := mul_le_mul_of_nonneg_left htilt (by positivity : (0 : ℝ) ≤ (ℓ : ℝ) + 1 / 2)
          nlinarith [mul_nonneg hKb hEσ]
  -- (iv) (12): the weighted weak equation, by transferring the graph part of (6) through `F`.
  have hW4 : ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) →
      ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ,
      |∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x| ≤
        (Kb + ℓ + 1) * (E + h) * M * σ ^ n := by
    intro ζ hζ hζc hζt M hM j
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hest := Submission.gwe_graph_tangential_estimate n ℓ hn U hU V H hH hmeas σ hσ hσU q f hf
      hfb hheight htan ζ hζ hζc hζt M hM j
    have htr : ∫ x in q '' graphOver f (ball 0 (σ / 4)), inner ℝ
          (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1)
          (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) ∂V.weight =
        ∫ x in ball (0 : Rn n) (σ / 4),
          inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x :=
      (hWi _ measurableSet_ball
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) _
        (hmeasg (fun y => f y j) ζ)).trans
        (by simp only [hfst, mul_comm (W _)])
    have hbad' : (V.weight (closedBall 0 (σ / 2) ∩
        (V.support \ q '' graphOver f (closedBall 0 (σ / 2))))).toReal ≤ Kb * E * σ ^ n :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (le_self_add.trans hbad)
    have hσn : σ * σ ^ (n - 1) = σ ^ n := by
      rw [← pow_succ']
      congr 1
      omega
    rw [htr] at hest
    calc _ ≤ _ := hest
      _ ≤ M * (Kb * E * σ ^ n) + M * (E * σ ^ n) + M * (σ / 4) * (h * σ ^ (n - 1)) := by
          gcongr
      _ = M * σ ^ n * (Kb * E + E + h / 4) := by
          rw [show M * (σ / 4) * (h * σ ^ (n - 1)) = M * h / 4 * (σ * σ ^ (n - 1)) by ring, hσn]
          ring
      _ ≤ M * σ ^ n * ((Kb + ℓ + 1) * (E + h)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hM0 (pow_nonneg hσ.le n))
          nlinarith [mul_nonneg hKb hh, mul_nonneg (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ) hE,
            mul_nonneg (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ) hh]
      _ = (Kb + ℓ + 1) * (E + h) * M * σ ^ n := by ring
  obtain ⟨hE16, hweak⟩ := hmain σ κ E h f W hσ hκ0 hκ1 hE hh hf hWm hW1 hW2 hW3
  exact ⟨hE16, fun ζ hζ hζc hζt M hM j => hweak ζ hζ hζc hζt M hM j (hW4 ζ hζ hζc hζt M hM j)⟩
/-- **Lemma A** of the tilt-excess decay (Simon Ch. 5, Lemma 2.1, p. 107, with an `L¹` curvature
term): if `spt V ∩ B_r(z)` lies within height `h` of `z + T`, `dim T = n`, then
`∫_{B_{r/2}(z)} |p_{T_x M} − p_T|² dμ_V ≤ 144 r⁻² ∫_{B_r(z)} dist(x − z, T)² dμ_V
  + 4h ∫_{B_r(z)} |H| dμ_V`.  Test the first variation with `X = ζ² p_{T⊥}(x − z)`, where
`ζ(x) = φ(|x − z|/r)`; then `div_M X = ζ² |p_x − p_T|²/2 + 2ζ ∇ζ · (p_x − p_T) x'` a.e., and the
cross term is absorbed by Young's inequality. -/
theorem ted_lemma_a_tilt_height : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → ∀ (z : Amb n ℓ) (r h : ℝ), 0 < r → closedBall z r ⊆ U → 0 ≤ h → ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → (∀ x ∈ V.support ∩ closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ≤ h) → ∫ x in closedBall z (r / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight ≤ 144 * (r ^ 2)⁻¹ * ∫ x in closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ^ 2 ∂V.weight + 4 * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
  intro n ℓ hn U hU V H hH hmeas hae z r h hr hBU hh T hT hht
  -- Step 1: the cutoff `ζ(x) = φ(|x - z|/r)` from the reused profile and gradient lemmas.
  obtain ⟨φ, hφs, hφ01, hφ1, hφ0, hφL⟩ := Submission.exists_smooth_step_profile_lipschitz_three
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : Amb n ℓ → ℝ, ζ = fun x => φ (‖x - z‖ / r) := ⟨_, rfl⟩
  have hζs : ContDiff ℝ (⊤ : ℕ∞) ζ := by
    rw [hζdef]
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x = z
    · subst hx
      have hev : (fun y => φ (‖y - x‖ / r)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [ball_mem_nhds x (half_pos hr)] with y hy
        apply hφ1
        rw [mem_ball, dist_eq_norm] at hy
        rw [div_le_iff₀ hr]
        linarith
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hne : x - z ≠ 0 := sub_ne_zero.2 hx
      have hnx : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Amb n ℓ => ‖y - z‖) x :=
        (contDiffAt_norm ℝ hne).comp x (contDiffAt_id.sub contDiffAt_const)
      exact hφs.contDiffAt.comp x (hnx.div_const r)
  have hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1 := fun x => by rw [hζdef]; exact hφ01 _
  have hζ1 : ∀ x ∈ closedBall z (r / 2), ζ x = 1 := fun x hx => by
    rw [hζdef]
    apply hφ1
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [div_le_iff₀ hr]
    linarith
  have hζ0 : ∀ x, r ≤ dist x z → ζ x = 0 := fun x hx => by
    rw [hζdef]
    apply hφ0
    rw [dist_eq_norm] at hx
    rw [le_div_iff₀ hr]
    linarith
  have hζd : ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / r := fun x => by
    rw [hζdef]
    simpa using Submission.norm_fderiv_radial_profile_le_of_lipschitzWith (n + ℓ) z r 3 φ hr hφL x
  -- The reused projection algebra: op-norm ≤ HS-norm, |p_{T⊥} v| = dist(v, T), trace identity.
  have hopHS : ∀ A : Amb n ℓ →L[ℝ] Amb n ℓ, ‖A‖ ≤ hsNorm A := fun A =>
    Submission.hsNorm_starProjection_trace_identities.1 (n + ℓ) (n + ℓ) A
  have hperp : ∀ v : Amb n ℓ, ‖Tᗮ.starProjection v‖ = infDist v (T : Set (Amb n ℓ)) :=
    fun v => Submission.hsNorm_starProjection_trace_identities.2.1 (n + ℓ) T v
  -- Notation: `g = |p_x - p_T|²`, `w = x' = p_{T⊥}(x - z)`, the cross term `b`, the field `X`.
  obtain ⟨g, hg⟩ : ∃ g : Amb n ℓ → ℝ, ∀ x, g x = hsNormSq (V.tangentProj x - T.starProjection) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Amb n ℓ → Amb n ℓ, ∀ x, w x = Tᗮ.starProjection (x - z) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Amb n ℓ → ℝ,
      ∀ x, b x = 2 * ζ x * fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Amb n ℓ → Amb n ℓ, ∀ x, X x = ζ x ^ 2 • w x := ⟨_, fun _ => rfl⟩
  -- Pointwise facts.
  have hζC1 : ContDiff ℝ 1 ζ := hζs.of_le (by exact_mod_cast le_top)
  have hζcont : Continuous ζ := hζC1.continuous
  have hDζcont : Continuous (fderiv ℝ ζ) := hζC1.continuous_fderiv one_ne_zero
  have hwcont : Continuous w := by
    rw [show w = fun x => Tᗮ.starProjection (x - z) from funext hw]
    fun_prop
  have hXcont : Continuous X := by
    rw [show X = fun x => ζ x ^ 2 • w x from funext hX]
    exact (hζcont.pow 2).smul hwcont
  have hζout : ∀ x, x ∉ closedBall z r → ζ x = 0 := fun x hx =>
    hζ0 x (not_le.1 fun hle => hx (mem_closedBall.2 hle)).le
  have hw_le : ∀ x, ‖w x‖ ≤ ‖x - z‖ := by
    intro x
    rw [hw]
    calc ‖Tᗮ.starProjection (x - z)‖ ≤ ‖Tᗮ.starProjection‖ * ‖x - z‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x - z‖ := by gcongr; exact Submodule.starProjection_norm_le _
      _ = ‖x - z‖ := one_mul _
  have hwB : ∀ x ∈ closedBall z r, ‖w x‖ ≤ r := fun x hx =>
    (hw_le x).trans (by rw [← dist_eq_norm]; exact mem_closedBall.1 hx)
  have hPnorm : ∀ x, ‖V.tangentProj x‖ ≤ 1 := by
    intro x
    unfold RectifiableVarifold.tangentProj
    split_ifs
    · exact Submodule.starProjection_norm_le _
    · simp
  have hA2 : ∀ x, ‖V.tangentProj x - T.starProjection‖ ≤ 2 := fun x =>
    (norm_sub_le _ _).trans (by linarith [hPnorm x, Submodule.starProjection_norm_le T])
  have hhs0 : ∀ A : Amb n ℓ →L[ℝ] Amb n ℓ, 0 ≤ hsNormSq A := fun A => by
    unfold hsNormSq
    positivity
  have hhs_le : ∀ A : Amb n ℓ →L[ℝ] Amb n ℓ, hsNormSq A ≤ (n + ℓ : ℕ) * ‖A‖ ^ 2 := by
    intro A
    unfold hsNormSq
    calc ∑ i : Fin (n + ℓ), ‖A (EuclideanSpace.single i 1)‖ ^ 2
        ≤ ∑ _i : Fin (n + ℓ), ‖A‖ ^ 2 := by
          gcongr with i
          calc ‖A (EuclideanSpace.single i 1)‖ ≤ ‖A‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
                A.le_opNorm _
            _ = ‖A‖ := by simp
      _ = (n + ℓ : ℕ) * ‖A‖ ^ 2 := by simp
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rw [hg]; exact hhs0 _
  have hgle : ∀ x, g x ≤ (n + ℓ : ℕ) * 4 := fun x => by
    rw [hg]
    refine (hhs_le _).trans ?_
    gcongr
    nlinarith [hA2 x, norm_nonneg (V.tangentProj x - T.starProjection)]
  -- `μ_V(B_r(z)) < ∞` (integrability of `θ` on compact subsets of `U`).
  have hμB : V.weight (closedBall z r) < ∞ := by
    have hint := V.integrableOn_mult (closedBall z r) (isCompact_closedBall z r) hBU
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact hint.lintegral_lt_top
  have : IsFiniteMeasure (V.weight.restrict (closedBall z r)) :=
    isFiniteMeasure_restrict.2 hμB.ne
  -- `μ_V`-a.e. point lies in `spt V = U ∩ spt μ_V`.
  have hsupp : ∀ᵐ x ∂V.weight, x ∈ V.support := by
    have h1 : ∀ᵐ x ∂V.weight, x ∈ V.weight.support := Measure.support_mem_ae
    have h2 : ∀ᵐ x ∂V.weight, x ∈ U := by
      have hac : V.weight ≪ (μHE[n] : Measure (Amb n ℓ)).restrict V.carrier :=
        withDensity_absolutelyContinuous _ _
      exact hac.ae_le ((ae_restrict_mem₀ V.nullMeasurableSet_carrier).mono
        fun x hx => V.carrier_subset hx)
    filter_upwards [h1, h2] with x hx1 hx2
    exact ⟨hx2, hx1⟩
  -- Measurability.
  have hPm : AEStronglyMeasurable (fun x => V.tangentProj x - T.starProjection)
      (V.weight.restrict (closedBall z r)) :=
    hmeas.restrict.sub aestronglyMeasurable_const
  have hgm : AEStronglyMeasurable g (V.weight.restrict (closedBall z r)) := by
    rw [show g = fun x => hsNormSq (V.tangentProj x - T.starProjection) from funext hg]
    have hcont : Continuous fun A : Amb n ℓ →L[ℝ] Amb n ℓ => hsNormSq A := by
      unfold hsNormSq
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_id.clm_apply continuous_const).norm).pow 2
    exact hcont.comp_aestronglyMeasurable hPm
  have hbm : AEStronglyMeasurable b (V.weight.restrict (closedBall z r)) := by
    rw [show b = fun x => 2 * ζ x * fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x))
      from funext hb]
    have happ : Continuous (Function.uncurry
        fun (A : Amb n ℓ →L[ℝ] Amb n ℓ) (v : Amb n ℓ) => A v) :=
      continuous_fst.clm_apply continuous_snd
    have happ' : Continuous (Function.uncurry
        fun (L : Amb n ℓ →L[ℝ] ℝ) (v : Amb n ℓ) => L v) :=
      continuous_fst.clm_apply continuous_snd
    exact (continuous_const.mul hζcont).aestronglyMeasurable.mul
      (happ'.comp_aestronglyMeasurable₂ hDζcont.aestronglyMeasurable
        (happ.comp_aestronglyMeasurable₂ hPm hwcont.aestronglyMeasurable))
  -- Integrability on `B_r(z)`.
  have hHint : Integrable H (V.weight.restrict (closedBall z r)) :=
    hH.1.integrableOn_compact_subset hBU (isCompact_closedBall z r)
  have hzg : Integrable (fun x => ζ x ^ 2 * g x) (V.weight.restrict (closedBall z r)) := by
    refine Integrable.of_bound ((hζcont.pow 2).aestronglyMeasurable.mul hgm) ((n + ℓ : ℕ) * 4)
      (ae_of_all _ fun x => ?_)
    obtain ⟨hz0, hz1⟩ := hζ01 x
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hg0 x))]
    calc ζ x ^ 2 * g x ≤ 1 * ((n + ℓ : ℕ) * 4) :=
          mul_le_mul (by nlinarith) (hgle x) (hg0 x) zero_le_one
      _ = (n + ℓ : ℕ) * 4 := one_mul _
  have hbi : Integrable b (V.weight.restrict (closedBall z r)) := by
    refine Integrable.of_bound hbm 12
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_))
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hD : ‖fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x))‖ ≤ 3 / r * (2 * r) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hζd x) ?_ (norm_nonneg _) (by positivity))
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hA2 x) (hwB x hx) (norm_nonneg _) zero_le_two)
    rw [hb, norm_mul, norm_mul, Real.norm_of_nonneg hz0, Real.norm_of_nonneg zero_le_two]
    calc 2 * ζ x * ‖fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x))‖
        ≤ 2 * 1 * (3 / r * (2 * r)) := by gcongr
      _ = 12 := by field_simp; norm_num
  have hh2 : Integrable (fun x => ‖w x‖ ^ 2) (V.weight.restrict (closedBall z r)) := by
    refine Integrable.of_bound (hwcont.norm.pow 2).aestronglyMeasurable (r ^ 2)
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hwB x hx) 2
  have hXH : Integrable (fun x => inner ℝ (X x) (H x)) (V.weight.restrict (closedBall z r)) := by
    refine Integrable.mono' (hHint.norm.const_mul r)
      (continuous_inner.comp_aestronglyMeasurable
        (hXcont.aestronglyMeasurable.prodMk hHint.aestronglyMeasurable))
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_))
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hz2 : ζ x ^ 2 ≤ 1 := by nlinarith
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    rw [hX, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
    calc ζ x ^ 2 * ‖w x‖ ≤ 1 * r := mul_le_mul hz2 (hwB x hx) (norm_nonneg _) zero_le_one
      _ = r := one_mul _
  -- Step 2: the test field `X = ζ² x'` is admissible.
  have hX1 : ContDiff ℝ 1 X := by
    rw [show X = fun x => ζ x ^ 2 • Tᗮ.starProjection (x - z) from funext fun x => by
      rw [hX, hw]]
    exact (hζC1.pow 2).smul ((Tᗮ.starProjection).contDiff.comp (contDiff_id.sub contDiff_const))
  have hXout : ∀ x, x ∉ closedBall z r → X x = 0 := fun x hx => by
    rw [hX, hζout x hx]
    simp
  have hXcs : HasCompactSupport X := HasCompactSupport.intro (isCompact_closedBall z r) hXout
  have hXts : tsupport X ⊆ U := by
    refine (closure_minimal (fun x hx => ?_) isClosed_closedBall).trans hBU
    by_contra hcon
    exact hx (hXout x hcon)
  -- Step 3: `div_M X = ζ² |p_x - p_T|²/2 + 2ζ ∇ζ · (p_x - p_T) x'` at a.e. point.
  have hdiv : ∀ᵐ x ∂V.weight, V.divM X x = 1 / 2 * (ζ x ^ 2 * g x) + b x := by
    filter_upwards [hae] with x hx
    obtain ⟨P, hP, hPx⟩ := hx
    rw [show X = fun y => ζ y ^ 2 • Tᗮ.starProjection (y - z) from funext fun y => by
      rw [hX, hw]]
    -- `DX(x) = ζ(x)² p_{T⊥} + (2ζ(x) Dζ(x)).smulRight x'`; trace against `p_x = p_P`.
    have hζx : DifferentiableAt ℝ ζ x := hζC1.differentiable one_ne_zero x
    have hsq : HasFDerivAt (fun y => ζ y ^ 2) ((2 * ζ x) • fderiv ℝ ζ x) x := by
      simpa using hζx.hasFDerivAt.pow 2
    have hlin : HasFDerivAt (fun y => Tᗮ.starProjection (y - z)) Tᗮ.starProjection x :=
      (Tᗮ.starProjection.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)).congr_fderiv
        (ContinuousLinearMap.comp_id _)
    have hXd := hsq.fun_smul hlin
    have hx' : T.starProjection (Tᗮ.starProjection (x - z)) = 0 :=
      (T.starProjection_apply_eq_zero_iff).mpr (Tᗮ.starProjection_apply_mem _)
    have htr : LinearMap.trace ℝ (Amb n ℓ)
        (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) =
          hsNormSq (P.starProjection - T.starProjection) / 2 :=
      Submission.hsNorm_starProjection_trace_identities.2.2 (n + ℓ) P T (hP.trans hT.symm)
    have hrk : (((2 * ζ x) • fderiv ℝ ζ x).smulRight (Tᗮ.starProjection (x - z))).toLinearMap ∘ₗ
        P.starProjection.toLinearMap =
          (((2 * ζ x) • fderiv ℝ ζ x).toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight
            (Tᗮ.starProjection (x - z)) := by
      ext v
      simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.smulRight_apply, LinearMap.smulRight_apply]
    rw [RectifiableVarifold.divM, hXd.fderiv, hPx, ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, LinearMap.add_comp, LinearMap.smul_comp, hrk, map_add,
      map_smul, htr, LinearMap.trace_smulRight, hg, hb, hw, hPx]
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe, smul_apply,
      smul_eq_mul, sub_apply, hx', sub_zero]
    ring
  -- Step 5: the first variation identity, localized to `B_r(z)`.
  have hFV := hH.2 X hX1 hXcs hXts
  have hL : ∫ x, V.divM X x ∂V.weight =
      ∫ x in closedBall z r, (1 / 2 * (ζ x ^ 2 * g x) + b x) ∂V.weight := by
    rw [integral_congr_ae hdiv]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    rw [hb, hζout x hx]
    ring
  have hR : ∫ x, inner ℝ (X x) (H x) ∂V.weight =
      ∫ x in closedBall z r, inner ℝ (X x) (H x) ∂V.weight :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hXout x hx, inner_zero_left]).symm
  -- Step 6: absorb the cross term (Young), and bound the curvature term by the height.
  have hb_bd : ∀ x, -b x ≤ 1 / 4 * (ζ x ^ 2 * g x) + 36 / r ^ 2 * ‖w x‖ ^ 2 := by
    intro x
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hsq : Real.sqrt (g x) ^ 2 = g x := Real.sq_sqrt (hg0 x)
    have hD : |fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x))| ≤
        3 / r * (Real.sqrt (g x) * ‖w x‖) := by
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hζd x) ?_ (norm_nonneg _) (by positivity))
      refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      rw [hg]
      exact hopHS _
    have h1 : -b x ≤ 2 * ζ x * (3 / r * (Real.sqrt (g x) * ‖w x‖)) := by
      rw [hb]
      calc -(2 * ζ x * fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x)))
          = 2 * ζ x * -fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (w x)) := by ring
        _ ≤ 2 * ζ x * (3 / r * (Real.sqrt (g x) * ‖w x‖)) :=
          mul_le_mul_of_nonneg_left ((neg_le_abs _).trans hD) (by positivity)
    have e : 1 / 4 * (ζ x ^ 2 * g x) + 36 / r ^ 2 * ‖w x‖ ^ 2 -
        2 * ζ x * (3 / r * (Real.sqrt (g x) * ‖w x‖)) =
        (ζ x * Real.sqrt (g x) / 2 - 6 / r * ‖w x‖) ^ 2 := by
      linear_combination (-(1 / 4) * ζ x ^ 2) * hsq
    linarith [sq_nonneg (ζ x * Real.sqrt (g x) / 2 - 6 / r * ‖w x‖)]
  have hXH_bd : ∀ᵐ x ∂(V.weight.restrict (closedBall z r)),
      -inner ℝ (X x) (H x) ≤ h * ‖H x‖ := by
    filter_upwards [ae_restrict_of_ae hsupp, ae_restrict_mem measurableSet_closedBall]
      with x hxs hxB
    obtain ⟨hz0, hz1⟩ := hζ01 x
    have hz2 : ζ x ^ 2 ≤ 1 := by nlinarith
    have hwh : ‖w x‖ ≤ h := by rw [hw, hperp]; exact hht x ⟨hxs, hxB⟩
    refine (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans ?_)
    gcongr
    rw [hX, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
    calc ζ x ^ 2 * ‖w x‖ ≤ 1 * h := mul_le_mul hz2 hwh (norm_nonneg _) zero_le_one
      _ = h := one_mul _
  have e1 : ∫ x in closedBall z r, (1 / 2 * (ζ x ^ 2 * g x) + b x) ∂V.weight =
      1 / 2 * ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight +
        ∫ x in closedBall z r, b x ∂V.weight := by
    rw [integral_add (hzg.const_mul _) hbi, integral_const_mul]
  have e2 : -∫ x in closedBall z r, b x ∂V.weight ≤
      1 / 4 * ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight +
        36 / r ^ 2 * ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight := by
    have hle := integral_mono hbi.neg ((hzg.const_mul (1 / 4)).add (hh2.const_mul (36 / r ^ 2)))
      hb_bd
    simp only [Pi.neg_apply, Pi.add_apply] at hle
    rwa [integral_neg, integral_add (hzg.const_mul _) (hh2.const_mul _), integral_const_mul,
      integral_const_mul] at hle
  have e3 : -∫ x in closedBall z r, inner ℝ (X x) (H x) ∂V.weight ≤
      h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
    have hle := integral_mono_ae hXH.neg (hHint.norm.const_mul h) hXH_bd
    simp only [Pi.neg_apply] at hle
    rwa [integral_neg, integral_const_mul] at hle
  have key : ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight ≤
      144 / r ^ 2 * ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight +
        4 * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight := by
    have hid := hFV
    rw [hL, hR, e1] at hid
    have r1 : 144 / r ^ 2 * ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight =
        4 * (36 / r ^ 2 * ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight) := by ring
    have r2 : 4 * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight =
        4 * (h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight) := by ring
    linarith
  -- Step 7: `ζ = 1` on `B_{r/2}(z)`, then rescale.
  have hB2 : ∫ x in closedBall z (r / 2), g x ∂V.weight ≤
      ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight := by
    calc ∫ x in closedBall z (r / 2), g x ∂V.weight
        = ∫ x in closedBall z (r / 2), ζ x ^ 2 * g x ∂V.weight :=
          setIntegral_congr_fun measurableSet_closedBall fun x hx => by rw [hζ1 x hx]; ring
      _ ≤ ∫ x in closedBall z r, ζ x ^ 2 * g x ∂V.weight :=
          setIntegral_mono_set hzg (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (hg0 x))
            (closedBall_subset_closedBall (by linarith)).eventuallyLE
  have hId : ∫ x in closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ^ 2 ∂V.weight =
      ∫ x in closedBall z r, ‖w x‖ ^ 2 ∂V.weight := by
    congr 1
    funext x
    rw [hw, hperp]
  have hgoal : ∫ x in closedBall z (r / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight =
      ∫ x in closedBall z (r / 2), g x ∂V.weight := by
    congr 1
    funext x
    rw [hg]
  rw [hgoal, hId, show (144 : ℝ) * (r ^ 2)⁻¹ = 144 / r ^ 2 by ring]
  exact hB2.trans key

set_option maxHeartbeats 1000000 in
/-- **Tilt-excess decay at the origin at the natural scale `σ = δρ`** (Simon Ch. 5, proof of
Theorem 4.5, steps (1)–(22)).  For `t ∈ (0, 1/128]` and `δ ≤ δ₁(t)`, to every `n`-plane `T` there
corresponds an `n`-plane `S` with `E(0, tδρ, S) ≤ C t² E_*(0, δρ, T)`, `C = C(n, ℓ, p)`. -/
theorem ted_decay_at_origin : TiltExcessHeightEstimate → AffineApproximationLemma → LipschitzApproximationLemma → HarmonicApproximationLemma → ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 128 → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₁ → V.AllardHypotheses H p δ ρ → ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → ∃ S : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S = n ∧ V.tiltExcess 0 (t * (δ * ρ)) S ≤ C * t ^ 2 * V.tiltExcessStar H p δ 0 (δ * ρ) T := by
  intro h21 h25 h26 h31 n ℓ hn p hp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hp1 : 1 ≤ p := by linarith only [hn1, hp]
  /- Elementary facts on Hilbert–Schmidt norms. -/
  have hhs0 : ∀ {m k : ℕ} (A : Rn m →L[ℝ] Rn k), 0 ≤ hsNormSq A := fun A => by
    unfold hsNormSq; positivity
  have hsq2 : ∀ a b c : ℝ, 0 ≤ c → c ≤ a + b → c ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    intro a b c hc hcab
    nlinarith [sq_nonneg (a - b)]
  have hhs_sub : ∀ {m k : ℕ} (B A : Rn m →L[ℝ] Rn k),
      hsNormSq (B - A) ≤ 2 * hsNormSq B + 2 * hsNormSq A := by
    intro m k B A
    unfold hsNormSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    gcongr with i
    rw [sub_apply]
    exact hsq2 _ _ _ (norm_nonneg _) (norm_sub_le _ _)
  have hhsle : ∀ A : Rn n →L[ℝ] Rn ℓ, hsNormSq A ≤ n * ‖A‖ ^ 2 := fun A => by
    unfold hsNormSq
    calc ∑ i : Fin n, ‖A (EuclideanSpace.single i 1)‖ ^ 2 ≤ ∑ _i : Fin n, ‖A‖ ^ 2 := by
          gcongr with i
          calc ‖A (EuclideanSpace.single i 1)‖ ≤ ‖A‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
                A.le_opNorm _
            _ = ‖A‖ := by simp
      _ = n * ‖A‖ ^ 2 := by simp
  /- Step 0: the constants; they depend only on `n, ℓ, p`.  As in the accepted natural proof:
  `C_R` bounds tilt and height of the reduced plane (`C₂ = C₃ = C_R`), `C_P, δ_P` come from the
  density bounds, `β₆, C₆` from 2.6, `C₂₁` from 2.1, `C_G` from the harmonic affine approximation and
  `C_W` from the weak equation; `C₄, …, C₁₉` are the derived constants (up to harmless enlargement)
  and `X` is the constant of the height-excess bound (20a). -/
  obtain ⟨CR, hCR, hSTP⟩ := Submission.tdo_small_tilt_plane h25 n ℓ hn p hp
  obtain ⟨CP, δP, hCP1, hδP, hδP8, hCPδP, hADB⟩ :=
    Submission.ted_allard_density_bounds n ℓ hn p hp
  obtain ⟨β6, C6, hβ6, -, hLAL⟩ := h26 n ℓ hn p hp
  obtain ⟨C21, hTEH⟩ := h21 n hn
  obtain ⟨CG, hCG, hHAA⟩ := Submission.ted_harmonic_affine_approx h31 n ℓ hn
  obtain ⟨CW, hCW, hGWE⟩ :=
    Submission.ted_graph_weak_equation n ℓ hn (max C6 1) (le_trans zero_le_one (le_max_right _ _))
  clear h21 h25 h26 h31
  have hCP : 0 < CP := lt_of_lt_of_le one_pos hCP1
  set C6' : ℝ := max C6 1 with hC6'def
  have hC6' : 0 < C6' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set C21' : ℝ := max C21 1 with hC21'def
  have hC21' : 0 < C21' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ω : ℝ := unitBallVolume n with hωdef
  have hω : 0 < ω :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  set cω : ℝ := max 1 (2 * ω) with hcωdef
  have hcω : 0 < cω := lt_of_lt_of_le one_pos (le_max_left _ _)
  -- the scaling factor in the Hölder bounds for `H`
  have hrpow : ∀ r s q : ℝ, 0 < r → r ≤ s → 0 < q → q ≤ p →
      (2 * (ω * r ^ n)) ^ (1 - q / p) * s ^ (q * ((n : ℝ) - p) / p) ≤ cω * r ^ ((n : ℝ) - q) := by
    intro r s q hr hrs hq hqp
    have hs : 0 < s := hr.trans_le hrs
    have ha0 : 0 ≤ 1 - q / p := by rw [sub_nonneg, div_le_one hp0]; exact hqp
    have ha1 : 1 - q / p ≤ 1 := by linarith only [div_pos hq hp0]
    have hb0 : 0 ≤ q - q * n / p := by
      rw [sub_nonneg, mul_div_assoc]
      exact mul_le_of_le_one_right hq.le ((div_le_one hp0).2 hp.le)
    have e1 : (2 * (ω * r ^ n)) ^ (1 - q / p) =
        (2 * ω) ^ (1 - q / p) * (r ^ ((n : ℝ) - q) * r ^ (q - q * n / p)) := by
      rw [show 2 * (ω * r ^ n) = (2 * ω) * r ^ n by ring, Real.mul_rpow (by positivity)
        (by positivity), ← Real.rpow_natCast r n, ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
      congr 2
      field_simp
      ring
    have e2 : s ^ (q * ((n : ℝ) - p) / p) = (s ^ (q - q * n / p))⁻¹ := by
      rw [← Real.rpow_neg hs.le]
      congr 1
      field_simp
      ring
    have hrs' : r ^ (q - q * n / p) / s ^ (q - q * n / p) ≤ 1 := by
      rw [← Real.div_rpow hr.le hs.le]
      exact Real.rpow_le_one (by positivity) (div_le_one_of_le₀ hrs hs.le) hb0
    have h2ω : (2 * ω) ^ (1 - q / p) ≤ cω := by
      rcases le_total (2 * ω) 1 with h | h
      · exact (Real.rpow_le_one (by positivity) h ha0).trans (le_max_left _ _)
      · calc (2 * ω) ^ (1 - q / p) ≤ (2 * ω) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h ha1
          _ = 2 * ω := Real.rpow_one _
          _ ≤ cω := le_max_right _ _
    rw [e1, e2]
    calc (2 * ω) ^ (1 - q / p) * (r ^ ((n : ℝ) - q) * r ^ (q - q * n / p)) *
          (s ^ (q - q * n / p))⁻¹
        = (2 * ω) ^ (1 - q / p) * r ^ ((n : ℝ) - q) *
            (r ^ (q - q * n / p) / s ^ (q - q * n / p)) := by ring
      _ ≤ cω * r ^ ((n : ℝ) - q) * 1 := by gcongr
      _ = cω * r ^ ((n : ℝ) - q) := mul_one _
  clear_value cω ω
  set C4 : ℝ := CR + 1 with hC4def
  have hC4 : 0 < C4 := by positivity
  set C9 : ℝ := 4 ^ n * CW with hC9def
  have hC9 : 0 < C9 := by positivity
  set C8 : ℝ := Real.sqrt C4 + cω + CP with hC8def
  have hC8 : 0 < C8 := by positivity
  set C11 : ℝ := CG * (CR + Real.sqrt C9 * Real.sqrt C4 / 4) with hC11def
  have hC11 : 0 < C11 := by positivity
  set C12 : ℝ := CG * Real.sqrt C9 with hC12def
  have hC12 : 0 < C12 := by positivity
  set C14 : ℝ := CR + C12 * Real.sqrt C4 + C11 with hC14def
  have hC14 : 0 < C14 := by positivity
  set X : ℝ := 4 * Real.sqrt 2 ^ n * CG * C9 + C14 ^ 2 * C6' with hXdef
  have hX : 0 < X := by positivity
  set C17 : ℝ := Real.sqrt (CG * C9) + Real.sqrt (CW + C12 ^ 2) with hC17def
  have hC17 : 0 ≤ C17 := by positivity
  set C18 : ℝ := 2 * C17 + 4 * C6' / ω with hC18def
  have hC18 : 0 ≤ C18 := by positivity
  set C19 : ℝ := C21' * (X + cω) + 288 * X + 2 * C18 * cω with hC19def
  have hC19 : 0 < C19 := by positivity
  clear_value C19 C18 C17 X C14 C12 C11 C8 C9 C4 C21' C6'
  refine ⟨2 ^ n * 256 * C19, by positivity, fun t ht ht128 => ?_⟩
  /- The choices depending on `t`: `η = 16 t`, `ε = η^{n+4}`, `δ_ε` and `δ₁`. -/
  have h16t : 16 * t ≤ 1 / 8 := by linarith only [ht128]
  set ε : ℝ := (16 * t) ^ (n + 4) with hεdef
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by
    calc ε = (16 * t) ^ (n + 4) := rfl
      _ ≤ (16 * t) ^ 1 :=
        pow_le_pow_of_le_one (by positivity) (by linarith only [h16t]) (by omega)
      _ < 1 := by rw [pow_one]; linarith only [h16t]
  obtain ⟨δε, hδε, hHAAε⟩ := hHAA ε hε0 hε1
  clear hHAA
  set κ₀ : ℝ := min (1 / C4) (min (1 / (16 * CR)) (min (δε * Real.sqrt C9 / (4 ^ n * CW * C8))
    (min (t / C11) (min (1 / (32 * C14)) (min ((16 * t) ^ 2 * (4 * t) ^ (n + 2))
      (t * (16 * t) ^ 2)))))) with hκ₀def
  have hκ₀ : 0 < κ₀ := by
    simp only [hκ₀def, lt_min_iff]
    exact ⟨by positivity, by positivity, by positivity, by positivity, by positivity,
      by positivity, by positivity⟩
  have hκ1 : κ₀ ≤ 1 / C4 := min_le_left _ _
  have hκ2 : κ₀ ≤ 1 / (16 * CR) := (min_le_right _ _).trans (min_le_left _ _)
  have hκ3 : κ₀ ≤ δε * Real.sqrt C9 / (4 ^ n * CW * C8) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκ4 : κ₀ ≤ t / C11 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have hκ5 : κ₀ ≤ 1 / (32 * C14) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hκ6 : κ₀ ≤ (16 * t) ^ 2 * (4 * t) ^ (n + 2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hκ7 : κ₀ ≤ t * (16 * t) ^ 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  clear_value κ₀
  refine ⟨min δP (min (β6 ^ (2 * n + 2)) (κ₀ ^ (2 * n + 2))), by positivity, ?_⟩
  intro U hU V H δ ρ hδ hδ₁ hAH T hT
  /- Step 1: smallness of `δ`, the scale `σ = δρ`, the power `d = δ^γ` and the density bounds. -/
  have hδP' : δ ≤ δP := hδ₁.trans (min_le_left _ _)
  have hδβ : δ ≤ β6 ^ (2 * n + 2) := hδ₁.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδκ : δ ≤ κ₀ ^ (2 * n + 2) := hδ₁.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ8 : δ ≤ 1 / 8 := hδP'.trans hδP8
  have hδ1 : δ ≤ 1 := by linarith only [hδ8]
  have hCPδ : CP * δ ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hδP' hCP.le).trans hCPδP
  clear hδ₁ hCPδP hδP8
  obtain ⟨hρ, hGMC, hθ1, h0spt, hBρU, -, hKρ⟩ := id hAH
  set σ : ℝ := δ * ρ with hσdef
  have hσ : 0 < σ := mul_pos hδ hρ
  have hσρ : σ ≤ ρ / 8 := by
    have := mul_le_mul_of_nonneg_right hδ8 hρ.le
    rw [hσdef]; linarith only [this]
  have h3σ : ∀ x : ℝ, x ≤ σ → x ≤ 3 * δ * ρ := fun x hx => by
    have : 3 * δ * ρ = 3 * σ := by rw [hσdef]; ring
    rw [this]; linarith only [hx, hσ]
  have hBσU : closedBall (0 : Amb n ℓ) σ ⊆ U :=
    (closedBall_subset_closedBall (by linarith only [hσρ, hρ])).trans hBρU
  set γ : ℝ := 1 / (2 * (n : ℝ) + 2) with hγdef
  have hγ0 : 0 < γ := by positivity
  have hγ2 : γ * 2 ≤ 1 := by
    rw [hγdef, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith only [hn1]
  set d : ℝ := δ ^ γ with hddef
  have hd0 : 0 < d := Real.rpow_pos_of_pos hδ γ
  have hd1 : d ≤ 1 := Real.rpow_le_one hδ.le hδ1 hγ0.le
  have hδd2 : δ ≤ d ^ 2 := by
    rw [hddef, ← Real.rpow_mul_natCast hδ.le]
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ (γ * ((2 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by push_cast; linarith only [hγ2])
  have hd2d : d ^ 2 ≤ d := by rw [sq]; exact mul_le_of_le_one_right hd0.le hd1
  have hδd : δ ≤ d := hδd2.trans hd2d
  have hsδ : Real.sqrt δ ≤ d := by
    rw [Real.sqrt_eq_rpow, hddef]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith only [hγ2])
  have hdκ : d ≤ κ₀ := by
    calc d = δ ^ γ := rfl
      _ ≤ (κ₀ ^ (2 * n + 2)) ^ γ := Real.rpow_le_rpow hδ.le hδκ hγ0.le
      _ = κ₀ := by
        rw [show γ = ((2 * n + 2 : ℕ) : ℝ)⁻¹ by rw [hγdef]; push_cast; ring]
        exact Real.pow_rpow_inv_natCast hκ₀.le (by omega)
  have hdC4 : C4 * d ^ 2 ≤ 1 := by
    calc C4 * d ^ 2 ≤ C4 * d := by gcongr
      _ ≤ C4 * (1 / C4) := by gcongr; exact hdκ.trans hκ1
      _ = 1 := by field_simp
  have hdCR : CR * d ≤ 1 / 16 := by
    calc CR * d ≤ CR * (1 / (16 * CR)) := by gcongr; exact hdκ.trans hκ2
      _ = 1 / 16 := by field_simp
  have hdtest : CW * C8 * d * 4 ^ n ≤ δε * Real.sqrt C9 := by
    calc CW * C8 * d * 4 ^ n = (4 ^ n * CW * C8) * d := by ring
      _ ≤ (4 ^ n * CW * C8) * (δε * Real.sqrt C9 / (4 ^ n * CW * C8)) := by
          gcongr; exact hdκ.trans hκ3
      _ = δε * Real.sqrt C9 := by field_simp
  have hdC11 : C11 * d ≤ t := by
    calc C11 * d ≤ C11 * (t / C11) := by gcongr; exact hdκ.trans hκ4
      _ = t := by field_simp
  have hdC14 : C14 * d ≤ 1 / 32 := by
    calc C14 * d ≤ C14 * (1 / (32 * C14)) := by gcongr; exact hdκ.trans hκ5
      _ = 1 / 32 := by field_simp
  have hdY : d ^ 2 ≤ (16 * t) ^ 2 * (4 * t) ^ (n + 2) := hd2d.trans (hdκ.trans hκ6)
  have hδt : δ ≤ (16 * t) ^ 2 :=
    hδd.trans (hdκ.trans (hκ7.trans
      (mul_le_of_le_one_left (by positivity) (by linarith only [ht128]))))
  have hsδt : Real.sqrt δ ≤ t * (16 * t) ^ 2 := hsδ.trans (hdκ.trans hκ7)
  clear hdκ hδκ hκ1 hκ2 hκ3 hκ4 hκ5 hκ6 hκ7 hκ₀ hκ₀def κ₀ hγ0 hγ2
  obtain ⟨hUp, hLow, hMult, hCarr⟩ := hADB U hU V H δ ρ hδ hδP' hAH
  clear hADB
  have hUp2 : ∀ y : Amb n ℓ, ‖y‖ ≤ σ → ∀ s : ℝ, 0 < s → s ≤ σ →
      V.weight (closedBall y s) ≤ ENNReal.ofReal (2 * (ω * s ^ n)) := by
    intro y hy s hs hsσ
    refine (hUp y (h3σ _ hy) s hs (by linarith only [hsσ, hσρ, hρ])).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (by linarith only [hCPδ]) (by positivity)
  have hLow2 : ∀ y ∈ V.support, ‖y‖ ≤ σ → ∀ s : ℝ, 0 < s → s ≤ σ →
      ENNReal.ofReal ((1 - CP * δ) * (ω * s ^ n)) ≤ V.weight (closedBall y s) :=
    fun y hy hyσ s hs hsσ => hLow y hy (h3σ _ hyσ) s hs (by linarith only [hsσ, hσρ, hρ])
  have hMult2 : ∀ᵐ x ∂V.weight, ‖x‖ ≤ σ → V.mult x ≤ 1 + CP * δ := by
    filter_upwards [hMult] with x hx hxσ
    exact hx (h3σ _ hxσ)
  clear hUp hLow hMult
  /- Step 2: reduction to a plane `T'` of small tilt and height (book (1), (2)). -/
  have hTPF := Submission.ted_tangent_plane_facts n ℓ hn U hU V
  have hmeas : AEStronglyMeasurable V.tangentProj V.weight := hTPF.2.2.1
  have hlow0 : ENNReal.ofReal (ω * σ ^ n / 2) ≤ V.weight (closedBall 0 σ) := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (hLow2 0 h0spt (by rw [norm_zero]; exact hσ.le) σ hσ le_rfl)
    calc ω * σ ^ n / 2 = (1 / 2) * (ω * σ ^ n) := by ring
      _ ≤ (1 - CP * δ) * (ω * σ ^ n) :=
        mul_le_mul_of_nonneg_right (by linarith only [hCPδ]) (by positivity)
  obtain ⟨T', hT'n, hT'star, hT'E, hT'h⟩ :=
    hSTP U hU V H δ ρ hδ (by linarith only [hδ8]) hAH hmeas hlow0 T hT
  have hT'star' : V.tiltExcessStar H p δ 0 σ T' ≤ V.tiltExcessStar H p δ 0 σ T := hT'star
  have hT'E' : V.tiltExcess 0 σ T' ≤ CR * d ^ 2 := hT'E
  have hT'h' : ∀ x ∈ V.support ∩ closedBall 0 (2 * σ),
      infDist x (T' : Set (Amb n ℓ)) ≤ CR * d * σ := hT'h
  clear hSTP hT'star hT'E hlow0
  -- the curvature term at scale `σ`: `K(0, σ) ≤ δ`
  have hK : V.scaledLpNorm H p 0 σ ≤ ENNReal.ofReal δ := by
    refine (Submission.tdo_scaledLpNorm_bounds.1 n ℓ U V H p 0 0 σ ρ hp0 hσ
      (by linarith only [hσρ, hρ]) (closedBall_subset_closedBall (by linarith only [hσρ, hρ]))).trans ?_
    calc ENNReal.ofReal ((σ / ρ) ^ ((p - n) / p)) * V.scaledLpNorm H p 0 ρ
        ≤ ENNReal.ofReal 1 * ENNReal.ofReal δ := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_one (by positivity) ?_
            (div_nonneg (sub_nonneg.2 hp.le) hp0.le))) hKρ
          rw [div_le_one hρ]; linarith only [hσρ, hρ]
      _ = ENNReal.ofReal δ := by rw [ENNReal.ofReal_one, one_mul]
  set k : ℝ := (V.scaledLpNorm H p 0 σ).toReal with hkdef
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hkδ : k ≤ δ := ENNReal.toReal_le_of_le_ofReal hδ.le hK
  have hKk : V.scaledLpNorm H p 0 σ ≤ ENNReal.ofReal k := by
    rw [hkdef, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK)]
  -- the excess `E₀ = E_*(0, σ, T')`
  set E0 : ℝ := V.tiltExcessStar H p δ 0 σ T' with hE0def
  have hE0eq : E0 = max (V.tiltExcess 0 σ T') (δ⁻¹ * k ^ 2) := rfl
  clear_value E0 k
  have hE0a : V.tiltExcess 0 σ T' ≤ E0 := by rw [hE0eq]; exact le_max_left _ _
  have hE0b : δ⁻¹ * k ^ 2 ≤ E0 := by rw [hE0eq]; exact le_max_right _ _
  have hE0nn : 0 ≤ E0 := le_trans (by positivity) hE0b
  have hE0C4 : E0 ≤ C4 * d ^ 2 := by
    rw [hE0eq]
    refine max_le (hT'E'.trans (mul_le_mul_of_nonneg_right
      (by rw [hC4def]; linarith only) (sq_nonneg d))) ?_
    calc δ⁻¹ * k ^ 2 ≤ δ⁻¹ * δ ^ 2 := by gcongr
      _ = δ := by field_simp
      _ ≤ d ^ 2 := hδd2
      _ ≤ C4 * d ^ 2 := le_mul_of_one_le_left (sq_nonneg d) (by rw [hC4def]; linarith only [hCR])
  have hE01 : E0 ≤ 1 := hE0C4.trans hdC4
  have hk2 : k ^ 2 ≤ δ * E0 := by
    have := mul_le_mul_of_nonneg_left hE0b hδ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul] at this
  have hksq : k ≤ Real.sqrt δ * Real.sqrt E0 := by
    rw [← Real.sqrt_mul hδ.le]
    exact (Real.le_sqrt hk0 (by positivity)).2 hk2
  have hsE0 : Real.sqrt E0 ≤ Real.sqrt C4 * d := by
    calc Real.sqrt E0 ≤ Real.sqrt (C4 * d ^ 2) := Real.sqrt_le_sqrt hE0C4
      _ = Real.sqrt C4 * d := by rw [Real.sqrt_mul hC4.le, Real.sqrt_sq hd0.le]
  have hstarT : 0 ≤ V.tiltExcessStar H p δ 0 σ T := le_max_of_le_right (by positivity)
  -- the trivial case `E₀ = 0`
  rcases hE0nn.eq_or_lt with hE0z | hE0pos
  · refine ⟨T', hT'n, ?_⟩
    have htσ : t * σ ≤ σ := mul_le_of_le_one_left hσ.le (by linarith only [ht128])
    have h1 := Submission.tdo_tiltExcess_le_of_subset n ℓ U V hmeas 0 0 (t * σ) σ T'
      (by positivity) htσ (closedBall_subset_closedBall htσ) hBσU
    calc V.tiltExcess 0 (t * σ) T' ≤ (σ / (t * σ)) ^ n * V.tiltExcess 0 σ T' := h1
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_le_of_eq hE0a hE0z.symm)
      _ ≤ 2 ^ n * 256 * C19 * t ^ 2 * V.tiltExcessStar H p δ 0 σ T := by positivity
  /- Step 2 (end): a rotation `q` with `q(ℝⁿ × {0}) = T'`. -/
  obtain ⟨q, hq⟩ := Submission.tdo_exists_isometry_rotatedPlane n ℓ T' hT'n
  /- Step 3: Lipschitz approximation (Simon 2.6 with `L = 1`, book (3), (4)). -/
  obtain ⟨f, hfLip0, hfsup0, hbad0⟩ := hLAL 1 CR one_pos le_rfl hCR.le U hU V H δ ρ hδ
    (by rw [mul_one]; exact hδβ) hAH q (by rw [hq]; exact hT'h)
  have hfLip : LipschitzOnWith 1 f (closedBall 0 (σ / 2)) := by
    simpa only [Real.toNNReal_one] using hfLip0
  have hfsup : ∀ x ∈ closedBall (0 : Rn n) (σ / 2), ‖f x‖ ≤ CR * d * σ := hfsup0
  clear hLAL hfLip0 hfsup0 hT'h hδβ
  clear_value d
  clear_value γ
  have hJ0 : 0 ≤ ∫ x in closedBall 0 σ,
      hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight :=
    integral_nonneg fun x => hhs0 _
  have hJ : ∫ x in closedBall 0 σ,
      hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight ≤ E0 * σ ^ n := by
    have h := hE0a
    rw [← hq] at h
    unfold RectifiableVarifold.tiltExcess at h
    rw [inv_mul_le_iff₀ (by positivity)] at h
    exact h.trans_eq (mul_comm _ _)
  have hbad : V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) +
      (μHE[n] : Measure (Amb n ℓ))
        (closedBall 0 (σ / 2) ∩ (q '' graphOver f (closedBall 0 (σ / 2)) \ V.support)) ≤
      ENNReal.ofReal (C6' * E0 * σ ^ n) := by
    refine hbad0.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [one_pow, inv_one, mul_one]
    calc C6 * ∫ x in closedBall 0 σ,
          hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight
        ≤ C6' * ∫ x in closedBall 0 σ,
          hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight :=
          mul_le_mul_of_nonneg_right (by rw [hC6'def]; exact le_max_left _ _) hJ0
      _ ≤ C6' * (E0 * σ ^ n) := mul_le_mul_of_nonneg_left hJ hC6'.le
      _ = C6' * E0 * σ ^ n := by ring
  clear hbad0 hJ0
  clear_value σ
  /- Step 4: the weak equation for `f` (book (15), (16)). -/
  have hgraph := hTPF.2.2.2.2 q f (σ / 2) 1 hfLip
  have hmult : ∀ᵐ x ∂V.weight, x ∈ closedBall 0 σ → 1 ≤ V.mult x ∧ V.mult x ≤ 1 + CP * δ := by
    filter_upwards [hθ1, hMult2] with x h1 h2 hx
    exact ⟨h1, h2 (mem_closedBall_zero_iff.1 hx)⟩
  have hcarr : (μHE[n] : Measure (Amb n ℓ)) ((V.support ∩ closedBall 0 σ) \ V.carrier) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left (inter_subset_inter_right _
      (closedBall_subset_ball (by linarith only [hσρ, hρ])))) hCarr
  -- Hölder for `|H|` on balls inside `B_σ(0)`
  have hHol1 : ∀ (z : Amb n ℓ) (s m : ℝ), 0 ≤ m → closedBall z s ⊆ closedBall 0 σ →
      V.weight (closedBall z s) ≤ ENNReal.ofReal m →
      ∫ x in closedBall z s, ‖H x‖ ∂V.weight ≤
        m ^ (1 - 1 / p) * σ ^ (1 * ((n : ℝ) - p) / p) * k := by
    intro z s m hm hsub hμ
    have hb := Submission.tdo_scaledLpNorm_bounds.2 n ℓ U V H p 1 z 0 s σ m one_pos hp1 hσ hm
      hsub hμ
    simp only [ENNReal.rpow_one] at hb
    have ha : 0 ≤ m ^ (1 - 1 / p) * σ ^ (1 * ((n : ℝ) - p) / p) := by positivity
    have hlin : ∫⁻ x in closedBall z s, ‖H x‖ₑ ∂V.weight ≤
        ENNReal.ofReal (m ^ (1 - 1 / p) * σ ^ (1 * ((n : ℝ) - p) / p) * k) := by
      rw [ENNReal.ofReal_mul ha]
      exact hb.trans (by gcongr)
    by_cases hm' : AEStronglyMeasurable (fun x => ‖H x‖) (V.weight.restrict (closedBall z s))
    · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => norm_nonneg _) hm']
      simp_rw [ofReal_norm]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
    · rw [integral_non_aestronglyMeasurable hm']
      positivity
  have hHσ : ∫ x in closedBall 0 (σ / 2), ‖H x‖ ∂V.weight ≤ cω * k * σ ^ (n - 1) := by
    have h1 := hHol1 0 (σ / 2) (2 * (ω * σ ^ n)) (by positivity)
      (closedBall_subset_closedBall (by linarith only [hσ]))
      ((measure_mono (closedBall_subset_closedBall (by linarith only [hσ]))).trans
        (hUp2 0 (by rw [norm_zero]; exact hσ.le) σ hσ le_rfl))
    have h2 := hrpow σ σ 1 hσ le_rfl one_pos hp1
    have h3 : σ ^ ((n : ℝ) - 1) = σ ^ (n - 1) := by
      rw [← Real.rpow_natCast, Nat.cast_sub hn, Nat.cast_one]
    calc ∫ x in closedBall 0 (σ / 2), ‖H x‖ ∂V.weight
        ≤ (2 * (ω * σ ^ n)) ^ (1 - 1 / p) * σ ^ (1 * ((n : ℝ) - p) / p) * k := h1
      _ ≤ cω * σ ^ ((n : ℝ) - 1) * k := mul_le_mul_of_nonneg_right h2 hk0
      _ = cω * k * σ ^ (n - 1) := by rw [h3]; ring
  have hfσ16 : ∀ x ∈ closedBall (0 : Rn n) (σ / 2), ‖f x‖ ≤ σ / 16 := fun x hx =>
    (hfsup x hx).trans (by have := mul_le_mul_of_nonneg_right hdCR hσ.le; linarith only [this])
  have hdistσ16 : ∀ x ∈ V.support ∩ closedBall 0 σ,
      infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ σ / 16 := by
    intro x hx
    rw [hq]
    refine (hT'h' x ⟨hx.1, closedBall_subset_closedBall (by linarith only [hσ]) hx.2⟩).trans ?_
    have := mul_le_mul_of_nonneg_right hdCR hσ.le
    linarith only [this]
  obtain ⟨h16, h15⟩ := hGWE U hU V H hGMC hmeas σ hσ hBσU q f hfLip hfσ16 hdistσ16 hgraph
    (CP * δ) E0 (cω * k) (by positivity) (by linarith only [hCPδ]) hE0nn (by positivity) hmult
    hcarr hJ hbad hHσ
  clear hGWE hgraph hmult hcarr hJ hHσ hfσ16 hdistσ16
  /- Step 5: harmonic and affine approximation (book (17)–(19)). -/
  have hint38 : IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) (ball (0 : Rn n) (3 * σ / 8)) := by
    have hcont : Continuous (fun A : Rn n →L[ℝ] Rn ℓ => hsNormSq A) :=
      continuous_finsetSum _ (fun i _ => (continuous_id.clm_apply continuous_const).norm.pow 2)
    have : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) (3 * σ / 8))) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    refine Integrable.of_bound (hcont.measurable.comp (measurable_fderiv ℝ f)).aestronglyMeasurable
      (n * 1 ^ 2) ((ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall
        (fun x hx => ?_)))
    rw [Real.norm_eq_abs, abs_of_nonneg (hhs0 _)]
    have hx' : x ∈ ball (0 : Rn n) (σ / 2) := ball_subset_ball (by linarith only [hσ]) hx
    have hD : ‖fderiv ℝ f x‖ ≤ 1 := by
      simpa using norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem hx') hfLip
    calc hsNormSq (fderiv ℝ f x) ≤ n * ‖fderiv ℝ f x‖ ^ 2 := hhsle _
      _ ≤ n * 1 ^ 2 := by gcongr
  have hDf : ∀ s : ℝ, s ≤ 3 * σ / 8 →
      ∫ x in ball (0 : Rn n) s, hsNormSq (fderiv ℝ f x) ≤ CW * E0 * σ ^ n := fun s hs =>
    (setIntegral_mono_set hint38 (ae_of_all _ fun x => hhs0 _)
      (ae_of_all _ (ball_subset_ball hs))).trans h16
  have htest : ∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ,
      |∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤
        δε * Real.sqrt (C9 * E0) * M * (σ / 4) ^ n := by
    intro ζ hζ hζc hζs M hM j
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    refine (h15 ζ (hζ.of_le (by exact_mod_cast le_top)) hζc hζs M hM j).trans ?_
    have hb1 : E0 ≤ Real.sqrt C4 * d * Real.sqrt E0 := by
      calc E0 = Real.sqrt E0 * Real.sqrt E0 := (Real.mul_self_sqrt hE0nn).symm
        _ ≤ Real.sqrt C4 * d * Real.sqrt E0 := by gcongr
    have hb2 : cω * k ≤ cω * d * Real.sqrt E0 := by
      calc cω * k ≤ cω * (Real.sqrt δ * Real.sqrt E0) := by gcongr
        _ ≤ cω * (d * Real.sqrt E0) := by gcongr
        _ = cω * d * Real.sqrt E0 := by ring
    have hb3 : CP * δ * Real.sqrt E0 ≤ CP * d * Real.sqrt E0 := by gcongr
    have hsum : E0 + cω * k + CP * δ * Real.sqrt E0 ≤ C8 * d * Real.sqrt E0 := by
      rw [hC8def]; linarith only [hb1, hb2, hb3]
    calc CW * (E0 + cω * k + CP * δ * Real.sqrt E0) * M * σ ^ n
        ≤ CW * (C8 * d * Real.sqrt E0) * M * σ ^ n := by gcongr
      _ = (CW * C8 * d * 4 ^ n) * Real.sqrt E0 * M * (σ / 4) ^ n := by
          rw [div_pow]; field_simp
      _ ≤ (δε * Real.sqrt C9) * Real.sqrt E0 * M * (σ / 4) ^ n := by gcongr
      _ = δε * Real.sqrt (C9 * E0) * M * (σ / 4) ^ n := by rw [Real.sqrt_mul hC9.le]; ring
  have hDfσ4 : ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x) ≤
      C9 * E0 * (σ / 4) ^ n := by
    refine (hDf (σ / 4) (by linarith only [hσ])).trans (le_of_eq ?_)
    rw [hC9def, div_pow]; field_simp
  obtain ⟨c, A, hA, hc, h19⟩ := hHAAε (σ / 4) (C9 * E0) (CR * d * σ) f 1 (by positivity)
    (by positivity) (by positivity) (hfLip.mono (closedBall_subset_closedBall
      (by linarith only [hσ])))
    (fun x hx => hfsup x (closedBall_subset_closedBall (by linarith only [hσ])
      (ball_subset_closedBall hx)))
    hDfσ4 htest
  clear hHAAε htest hDfσ4 h15 h16
  have hAnn : 0 ≤ hsNorm A := Real.sqrt_nonneg _
  have hA' : hsNorm A ≤ C12 * Real.sqrt E0 := by
    rw [hC12def, mul_assoc, ← Real.sqrt_mul hC9.le]; exact hA
  have hc' : ‖c‖ ≤ C11 * d * σ := by
    refine hc.trans ?_
    have h1 : Real.sqrt (ε * (C9 * E0)) ≤ Real.sqrt C9 * (Real.sqrt C4 * d) := by
      calc Real.sqrt (ε * (C9 * E0)) ≤ Real.sqrt (C9 * E0) :=
            Real.sqrt_le_sqrt (mul_le_of_le_one_left (by positivity) hε1.le)
        _ = Real.sqrt C9 * Real.sqrt E0 := Real.sqrt_mul hC9.le _
        _ ≤ Real.sqrt C9 * (Real.sqrt C4 * d) := by gcongr
    calc CG * (CR * d * σ + σ / 4 * Real.sqrt (ε * (C9 * E0)))
        ≤ CG * (CR * d * σ + σ / 4 * (Real.sqrt C9 * (Real.sqrt C4 * d))) := by gcongr
      _ = C11 * d * σ := by rw [hC11def]; ring
  have hcτ : ‖c‖ ≤ t * σ :=
    hc'.trans (by have := mul_le_mul_of_nonneg_right hdC11 hσ.le; linarith only [this])
  /- Step 6: tilt from height (book (20)). -/
  obtain ⟨hSdim, hSdist, -, -, hτnorm⟩ := Submission.tdo_graph_plane_dist n ℓ q A
  set S : Submodule ℝ (Amb n ℓ) :=
    Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) with hSdef
  set τ : Amb n ℓ := q (graphPoint (0 : Rn n) c) with hτdef
  have hτc : ‖τ‖ = ‖c‖ := hτnorm c
  have htσ : t * σ ≤ σ / 128 := by
    have := mul_le_mul_of_nonneg_right ht128 hσ.le; linarith only [this]
  have hτ : ‖τ‖ ≤ t * σ := hτc.trans_le hcτ
  set r : ℝ := 16 * t * (σ / 4) with hrdef
  have hr : 0 < r := by positivity
  have hrσ : r ≤ σ / 32 := by rw [hrdef]; linarith only [htσ]
  have hBτr : closedBall τ r ⊆ closedBall 0 (σ / 2) :=
    closedBall_subset_closedBall' (by rw [dist_zero_right]; linarith only [hrσ, hτ, htσ, hσ])
  have hBτσ : closedBall τ r ⊆ closedBall 0 σ :=
    hBτr.trans (closedBall_subset_closedBall (by linarith only [hσ]))
  have hBσ2U : closedBall (0 : Amb n ℓ) (σ / 2) ⊆ U :=
    (closedBall_subset_closedBall (by linarith only [hσ])).trans hBσU
  have hBτrU : closedBall τ r ⊆ U := hBτσ.trans hBσU
  have hμτ : V.weight (closedBall τ r) ≤ ENNReal.ofReal (2 * (ω * r ^ n)) :=
    hUp2 τ (by linarith only [hτ, htσ, hσ]) r hr (by linarith only [hrσ, hσ])
  -- heights of `spt V` near `τ` over the plane `S`
  have hheight : ∀ x ∈ V.support ∩ closedBall τ r,
      infDist (x - τ) (S : Set (Amb n ℓ)) ≤ C14 * d * σ := by
    intro x hx
    have hxσ : ‖x‖ ≤ σ := mem_closedBall_zero_iff.1 (hBτσ hx.2)
    have h1 : infDist (x - τ) (S : Set (Amb n ℓ)) ≤ infDist x (S : Set (Amb n ℓ)) + ‖τ‖ := by
      have := infDist_le_infDist_add_dist (s := (S : Set (Amb n ℓ))) (x := x - τ) (y := x)
      rwa [dist_eq_norm, sub_sub_cancel_left, norm_neg] at this
    have h2 := hSdist x
    rw [hq] at h2
    have h3 := hT'h' x ⟨hx.1, mem_closedBall_zero_iff.2 (by linarith only [hxσ, hσ])⟩
    have h4 : hsNorm A * ‖x‖ ≤ C12 * (Real.sqrt C4 * d) * σ :=
      mul_le_mul (hA'.trans (by gcongr)) hxσ (norm_nonneg _) (by positivity)
    calc infDist (x - τ) (S : Set (Amb n ℓ))
        ≤ CR * d * σ + C12 * (Real.sqrt C4 * d) * σ + C11 * d * σ := by
          linarith only [h1, h2, h3, h4, hτc, hc']
      _ = C14 * d * σ := by rw [hC14def]; ring
  -- the height excess near `τ` (book (20a))
  have hmult2 : ∀ᵐ x ∂V.weight, x ∈ closedBall τ r → V.mult x ≤ 2 := by
    filter_upwards [hMult2] with x hx hxB
    have := hx (mem_closedBall_zero_iff.1 (hBτσ hxB))
    linarith only [this, hCPδ]
  have hbad1 : V.weight (closedBall 0 (σ / 2) ∩
      (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) ≤ ENNReal.ofReal (C6' * E0 * σ ^ n) :=
    le_trans le_self_add hbad
  set Q : ℝ := ∫ x in closedBall τ r, infDist (x - τ) (S : Set (Amb n ℓ)) ^ 2 ∂V.weight with hQdef
  have hQ0 : 0 ≤ Q := integral_nonneg fun x => sq_nonneg _
  have hGHE : Q ≤ 2 * Real.sqrt 2 ^ n * (∫ x in ball (0 : Rn n) r, ‖f x - (c + A x)‖ ^ 2) +
      (C14 * d * σ) ^ 2 * (C6' * E0 * σ ^ n) :=
    Submission.tdo_graph_height_excess n ℓ U V q f c A (σ / 2) r (C14 * d * σ) (C6' * E0 * σ ^ n)
      hr (by linarith only [hrσ, hσ]) hBσ2U hfLip hBτr (by positivity) hmult2 hheight hbad1
  clear_value Q
  have h19e : ∫ x in ball (0 : Rn n) r, ‖f x - (c + A x)‖ ^ 2 ≤
      CG * (ε + ε) * (C9 * E0) * (σ / 4) ^ (n + 2) :=
    h19 (16 * t) (by positivity) (by linarith only [h16t])
  clear_value r ε
  have ha : (16 * t) ^ (n + 4) * (σ / 4) ^ (n + 2) = (16 * t) ^ 2 * r ^ (n + 2) := by
    calc (16 * t) ^ (n + 4) * (σ / 4) ^ (n + 2)
        = (16 * t) ^ 2 * ((16 * t) ^ (n + 2) * (σ / 4) ^ (n + 2)) := by ring
      _ = (16 * t) ^ 2 * r ^ (n + 2) := by rw [hrdef, ← mul_pow]
  have hb : (4 * t) ^ (n + 2) * σ ^ (n + 2) = r ^ (n + 2) := by
    rw [← mul_pow, hrdef]; congr 1; ring
  have h20a : Q ≤ X * (16 * t) ^ 2 * E0 * r ^ (n + 2) := by
    calc Q ≤ 2 * Real.sqrt 2 ^ n * (∫ x in ball (0 : Rn n) r, ‖f x - (c + A x)‖ ^ 2) +
          (C14 * d * σ) ^ 2 * (C6' * E0 * σ ^ n) := hGHE
      _ ≤ 2 * Real.sqrt 2 ^ n * (CG * (ε + ε) * (C9 * E0) * (σ / 4) ^ (n + 2)) +
          (C14 * d * σ) ^ 2 * (C6' * E0 * σ ^ n) := by gcongr
      _ = 4 * Real.sqrt 2 ^ n * CG * C9 * (16 * t) ^ 2 * E0 * r ^ (n + 2) +
          C14 ^ 2 * C6' * d ^ 2 * E0 * σ ^ (n + 2) := by
          rw [hεdef]; linear_combination (4 * Real.sqrt 2 ^ n * CG * C9 * E0) * ha
      _ ≤ 4 * Real.sqrt 2 ^ n * CG * C9 * (16 * t) ^ 2 * E0 * r ^ (n + 2) +
          C14 ^ 2 * C6' * ((16 * t) ^ 2 * (4 * t) ^ (n + 2)) * E0 * σ ^ (n + 2) := by gcongr
      _ = X * (16 * t) ^ 2 * E0 * r ^ (n + 2) := by
          rw [hXdef]; linear_combination (C14 ^ 2 * C6' * (16 * t) ^ 2 * E0) * hb
  /- The tilt bound (book (20)) in the two curvature regimes. -/
  have h20 : V.tiltExcess τ (r / 2) S ≤ C19 * (16 * t) ^ 2 * E0 := by
    rcases le_or_gt 2 p with hp2 | hp2
    · -- Case `p ≥ 2`: Simon 2.1 at `(τ, r, S)` with the `L²` Hölder bound for `H`.
      have h21i := hTEH ℓ U hU V H hGMC τ r hr hBτrU S hSdim
      set Y : ℝ := (2 * (ω * r ^ n)) ^ (1 - 2 / p) * σ ^ (2 * ((n : ℝ) - p) / p) * k ^ 2
        with hYdef
      have hY0 : 0 ≤ Y := by positivity
      clear_value Y
      have hHs : ∫⁻ x in closedBall τ r, ‖H x‖ₑ ^ 2 ∂V.weight ≤ ENNReal.ofReal Y := by
        have hb2 := Submission.tdo_scaledLpNorm_bounds.2 n ℓ U V H p 2 τ 0 r σ (2 * (ω * r ^ n))
          two_pos hp2 hσ (by positivity) hBτσ hμτ
        simp only [ENNReal.rpow_two] at hb2
        rw [hYdef, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hk0]
        exact hb2.trans (by gcongr)
      have hdiv : ∫ x in closedBall τ r, (infDist (x - τ) (S : Set (Amb n ℓ)) / r) ^ 2 ∂V.weight =
          Q / r ^ 2 := by
        rw [hQdef]; simp_rw [div_pow]; exact integral_div _ _
      have hC21le : C21 ≤ C21' := by rw [hC21'def]; exact le_max_left _ _
      have ha0 : 0 ≤ C21' * (r ^ n)⁻¹ * (Q / r ^ 2) := by positivity
      have hb0 : 0 ≤ C21' * r ^ ((2 : ℝ) - n) * Y := by positivity
      have hE : V.tiltExcess τ (r / 2) S ≤
          C21' * (r ^ n)⁻¹ * (Q / r ^ 2) + C21' * r ^ ((2 : ℝ) - n) * Y := by
        rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg ha0 hb0), ENNReal.ofReal_add ha0 hb0,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C21' * r ^ ((2 : ℝ) - n))]
        refine h21i.trans (add_le_add ?_ ?_)
        · rw [hdiv]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC21le (by positivity)) (by positivity))
        · exact mul_le_mul' (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right hC21le (by positivity))) hHs
      have hQr : (r ^ n)⁻¹ * (Q / r ^ 2) ≤ X * (16 * t) ^ 2 * E0 := by
        rw [show (r ^ n)⁻¹ * (Q / r ^ 2) = Q / r ^ (n + 2) by rw [pow_add]; field_simp,
          div_le_iff₀ (by positivity)]
        exact h20a
      have hrr : r ^ ((2 : ℝ) - n) * r ^ ((n : ℝ) - 2) = 1 := by
        rw [← Real.rpow_add hr, show (2 : ℝ) - n + (n - 2) = 0 by ring, Real.rpow_zero]
      have hYb : r ^ ((2 : ℝ) - n) * Y ≤ cω * (δ * E0) := by
        have h1 := hrpow r σ 2 hr (by linarith only [hrσ, hσ]) two_pos hp2
        calc r ^ ((2 : ℝ) - n) * Y ≤ r ^ ((2 : ℝ) - n) * (cω * r ^ ((n : ℝ) - 2) * k ^ 2) := by
              rw [hYdef]; gcongr
          _ = cω * k ^ 2 * (r ^ ((2 : ℝ) - n) * r ^ ((n : ℝ) - 2)) := by ring
          _ = cω * k ^ 2 := by rw [hrr, mul_one]
          _ ≤ cω * (δ * E0) := by gcongr
      calc V.tiltExcess τ (r / 2) S
          ≤ C21' * (r ^ n)⁻¹ * (Q / r ^ 2) + C21' * r ^ ((2 : ℝ) - n) * Y := hE
        _ = C21' * ((r ^ n)⁻¹ * (Q / r ^ 2)) + C21' * (r ^ ((2 : ℝ) - n) * Y) := by ring
        _ ≤ C21' * (X * (16 * t) ^ 2 * E0) + C21' * (cω * (δ * E0)) := by gcongr
        _ ≤ C21' * (X * (16 * t) ^ 2 * E0) + C21' * (cω * ((16 * t) ^ 2 * E0)) := by gcongr
        _ = C21' * (X + cω) * (16 * t) ^ 2 * E0 := by ring
        _ ≤ C19 * (16 * t) ^ 2 * E0 := by
            gcongr
            rw [hC19def]
            have : 0 ≤ 288 * X + 2 * C18 * cω := by positivity
            linarith only [this]
    · -- Case `n < p < 2`, so `n = 1`: Lemma A with the one-dimensional sup bound.
      obtain rfl : n = 1 := by
        have h2 : (n : ℝ) < 2 := hp.trans hp2
        have : n < 2 := by exact_mod_cast h2
        omega
      -- `|f - λ| ≤ C₁₇ σ E₀^{1/2}` on `B¹_{σ/16}`
      have hwLip := (hfLip.mono (closedBall_subset_closedBall (by linarith only [hσ]) :
          closedBall (0 : Rn 1) (σ / 16) ⊆ closedBall 0 (σ / 2))).sub
        ((LipschitzWith.const c).add A.lipschitzWith).lipschitzOnWith
      have hsup1 : ∀ x ∈ closedBall (0 : Rn 1) (σ / 16), ‖f x - (c + A x)‖ ≤
          Real.sqrt ((2 * (σ / 16))⁻¹ * ∫ y in ball (0 : Rn 1) (σ / 16), ‖f y - (c + A y)‖ ^ 2) +
          Real.sqrt (2 * (σ / 16) * ∫ y in ball (0 : Rn 1) (σ / 16),
            hsNormSq (fderiv ℝ (fun x => f x - (c + A x)) y)) :=
        Submission.tdo_one_dim_sup_le ℓ (fun x => f x - (c + A x)) (σ / 16) _ (by positivity) hwLip
      have hw2 : ∫ y in ball (0 : Rn 1) (σ / 16), ‖f y - (c + A y)‖ ^ 2 ≤
          CG * (ε + (1 / 4) ^ (1 + 4)) * (C9 * E0) * (σ / 4) ^ (1 + 2) := by
        have h := h19 (1 / 4) (by norm_num) le_rfl
        rwa [show (1 : ℝ) / 4 * (σ / 4) = σ / 16 by ring] at h
      have hDw : ∀ y, hsNormSq (fderiv ℝ (fun x => f x - (c + A x)) y) ≤
          2 * hsNormSq (fderiv ℝ f y) + 2 * hsNormSq A := by
        intro y
        have hlam : DifferentiableAt ℝ (fun x => c + A x) y :=
          (differentiableAt_const c).add A.differentiableAt
        by_cases hfy : DifferentiableAt ℝ f y
        · rw [fderiv_fun_sub hfy hlam, fderiv_const_add, ContinuousLinearMap.fderiv]
          exact hhs_sub _ _
        · have hw : ¬ DifferentiableAt ℝ (fun x => f x - (c + A x)) y := fun hw =>
            hfy (by simpa using hw.add hlam)
          rw [fderiv_zero_of_not_differentiableAt hw]
          have h0 : hsNormSq (0 : Rn 1 →L[ℝ] Rn ℓ) = 0 := by simp [hsNormSq]
          rw [h0]
          have := hhs0 (fderiv ℝ f y)
          have := hhs0 A
          positivity
      have hvol : volume (ball (0 : Rn 1) (σ / 16)) = ENNReal.ofReal (2 * (σ / 16)) := by
        rw [EuclideanSpace.volume_ball (Fin 1) 0 (σ / 16)]
        simp only [Fintype.card_fin, pow_one, Nat.cast_one]
        have hΓ : Real.Gamma (1 / 2 + 1) = Real.sqrt Real.pi / 2 := by
          rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
        rw [hΓ, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
        field_simp
      have hIf : IntegrableOn (fun y => hsNormSq (fderiv ℝ f y)) (ball (0 : Rn 1) (σ / 16)) :=
        hint38.mono_set (ball_subset_ball (by linarith only [hσ]))
      have hIc : IntegrableOn (fun _ : Rn 1 => 2 * hsNormSq A) (ball (0 : Rn 1) (σ / 16)) :=
        integrableOn_const (by rw [hvol]; exact ENNReal.ofReal_ne_top)
      have hDwI : ∫ y in ball (0 : Rn 1) (σ / 16), hsNormSq (fderiv ℝ (fun x => f x - (c + A x)) y) ≤
          2 * (CW * E0 * σ ^ 1) + 2 * hsNormSq A * (2 * (σ / 16)) := by
        calc ∫ y in ball (0 : Rn 1) (σ / 16), hsNormSq (fderiv ℝ (fun x => f x - (c + A x)) y)
            ≤ ∫ y in ball (0 : Rn 1) (σ / 16), (2 * hsNormSq (fderiv ℝ f y) + 2 * hsNormSq A) :=
              integral_mono_of_nonneg (ae_of_all _ fun y => hhs0 _) ((hIf.const_mul 2).add hIc)
                (ae_of_all _ hDw)
          _ = 2 * (∫ y in ball (0 : Rn 1) (σ / 16), hsNormSq (fderiv ℝ f y)) +
                2 * hsNormSq A * (2 * (σ / 16)) := by
              rw [integral_add (hIf.const_mul 2) hIc, integral_const_mul, setIntegral_const,
                measureReal_def, hvol, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
              ring
          _ ≤ 2 * (CW * E0 * σ ^ 1) + 2 * hsNormSq A * (2 * (σ / 16)) := by
              gcongr
              exact hDf _ (by linarith only [hσ])
      have hAsq : hsNormSq A ≤ C12 ^ 2 * E0 := by
        rw [show hsNormSq A = hsNorm A ^ 2 from (Real.sq_sqrt (hhs0 A)).symm]
        calc hsNorm A ^ 2 ≤ (C12 * Real.sqrt E0) ^ 2 := pow_le_pow_left₀ hAnn hA' 2
          _ = C12 ^ 2 * E0 := by rw [mul_pow, Real.sq_sqrt hE0nn]
      have hsupb : ∀ x' ∈ closedBall (0 : Rn 1) (σ / 16),
          ‖f x' - (c + A x')‖ ≤ C17 * σ * Real.sqrt E0 := by
        intro x' hx'
        refine (hsup1 x' hx').trans ?_
        have hs1 : Real.sqrt ((2 * (σ / 16))⁻¹ * ∫ y in ball (0 : Rn 1) (σ / 16),
            ‖f y - (c + A y)‖ ^ 2) ≤ Real.sqrt (CG * C9) * σ * Real.sqrt E0 := by
          have e : Real.sqrt (CG * C9 * σ ^ 2 * E0) = Real.sqrt (CG * C9) * σ * Real.sqrt E0 := by
            rw [Real.sqrt_mul' _ hE0nn, Real.sqrt_mul' _ (sq_nonneg σ), Real.sqrt_sq hσ.le]
          rw [← e]
          apply Real.sqrt_le_sqrt
          calc (2 * (σ / 16))⁻¹ * ∫ y in ball (0 : Rn 1) (σ / 16), ‖f y - (c + A y)‖ ^ 2
              ≤ (2 * (σ / 16))⁻¹ * (CG * (ε + (1 / 4) ^ (1 + 4)) * (C9 * E0) * (σ / 4) ^ (1 + 2)) := by
                gcongr
            _ = CG * C9 * σ ^ 2 * E0 * ((ε + 1 / 1024) / 8) := by field_simp; ring
            _ ≤ CG * C9 * σ ^ 2 * E0 * 1 := by gcongr; linarith only [hε1]
            _ = CG * C9 * σ ^ 2 * E0 := mul_one _
        have hs2 : Real.sqrt (2 * (σ / 16) * ∫ y in ball (0 : Rn 1) (σ / 16),
            hsNormSq (fderiv ℝ (fun x => f x - (c + A x)) y)) ≤
            Real.sqrt (CW + C12 ^ 2) * σ * Real.sqrt E0 := by
          have e : Real.sqrt ((CW + C12 ^ 2) * σ ^ 2 * E0) =
              Real.sqrt (CW + C12 ^ 2) * σ * Real.sqrt E0 := by
            rw [Real.sqrt_mul' _ hE0nn, Real.sqrt_mul' _ (sq_nonneg σ), Real.sqrt_sq hσ.le]
          rw [← e]
          apply Real.sqrt_le_sqrt
          calc 2 * (σ / 16) * ∫ y in ball (0 : Rn 1) (σ / 16),
                hsNormSq (fderiv ℝ (fun x => f x - (c + A x)) y)
              ≤ 2 * (σ / 16) * (2 * (CW * E0 * σ ^ 1) + 2 * (C12 ^ 2 * E0) * (2 * (σ / 16))) := by
                gcongr
                exact hDwI.trans (by gcongr)
            _ = (CW / 4 + C12 ^ 2 / 32) * σ ^ 2 * E0 := by ring
            _ ≤ (CW + C12 ^ 2) * σ ^ 2 * E0 := by
                gcongr <;> linarith only [hCW, sq_nonneg C12]
        calc _ ≤ Real.sqrt (CG * C9) * σ * Real.sqrt E0 +
              Real.sqrt (CW + C12 ^ 2) * σ * Real.sqrt E0 := add_le_add hs1 hs2
          _ = C17 * σ * Real.sqrt E0 := by rw [hC17def]; ring
      -- the sup of the heights over `S` near `τ`
      set κ : ℝ := (1 - CP * δ) * ω with hκdef
      clear_value κ
      have hκω : ω / 2 ≤ κ := by
        rw [hκdef]
        calc ω / 2 = (1 / 2) * ω := by ring
          _ ≤ (1 - CP * δ) * ω := mul_le_mul_of_nonneg_right (by linarith only [hCPδ]) hω.le
      have hκ : 0 < κ := lt_of_lt_of_le (by positivity) hκω
      have hlowκ : ∀ x ∈ V.support ∩ closedBall τ r, ∀ s : ℝ, 0 < s → s ≤ σ / 64 →
          ENNReal.ofReal (κ * s) ≤ V.weight (closedBall x s) := by
        intro x hx s hs hs'
        have h1 := hLow2 x hx.1 (mem_closedBall_zero_iff.1 (hBτσ hx.2)) s hs
          (by linarith only [hs', hσ])
        rw [pow_one] at h1
        calc ENNReal.ofReal (κ * s) = ENNReal.ofReal ((1 - CP * δ) * (ω * s)) := by
              rw [hκdef, mul_assoc]
          _ ≤ V.weight (closedBall x s) := h1
      have hheight2 : ∀ x ∈ V.support ∩ closedBall τ r,
          infDist (x - τ) (S : Set (Amb 1 ℓ)) ≤ 2 * (σ / 64) := by
        intro x hx
        refine (hheight x hx).trans ?_
        have := mul_le_mul_of_nonneg_right hdC14 hσ.le
        linarith only [this]
      have hHS : ∀ x ∈ V.support ∩ closedBall τ r, infDist (x - τ) (S : Set (Amb 1 ℓ)) ≤
          max (2 * (C17 * σ * Real.sqrt E0)) (2 * (C6' * E0 * σ ^ 1) / κ) :=
        Submission.tdo_graph_height_sup 1 ℓ U V q f c A (σ / 2) (σ / 16) r (σ / 64)
          (C17 * σ * Real.sqrt E0) (C6' * E0 * σ ^ 1) κ (by positivity) hκ
          (by linarith only [hrσ, hσ]) (by linarith only [hcτ, htσ, hrσ, hσ]) hsupb hbad1 hlowκ
          hheight2
      have hE0s : E0 ≤ Real.sqrt E0 := by
        calc E0 = Real.sqrt E0 * Real.sqrt E0 := (Real.mul_self_sqrt hE0nn).symm
          _ ≤ Real.sqrt E0 * 1 := by gcongr; exact Real.sqrt_le_one.2 hE01
          _ = Real.sqrt E0 := mul_one _
      have hhstar : ∀ x ∈ V.support ∩ closedBall τ r,
          infDist (x - τ) (S : Set (Amb 1 ℓ)) ≤ C18 * σ * Real.sqrt E0 := by
        intro x hx
        refine (hHS x hx).trans (max_le ?_ ?_)
        · rw [hC18def]
          have : 0 ≤ 4 * C6' / ω * σ * Real.sqrt E0 := by positivity
          linarith only [this]
        · calc 2 * (C6' * E0 * σ ^ 1) / κ ≤ 2 * (C6' * E0 * σ ^ 1) / (ω / 2) :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hκω
            _ = 4 * C6' / ω * σ * E0 := by field_simp; ring
            _ ≤ 4 * C6' / ω * σ * Real.sqrt E0 := by gcongr
            _ ≤ C18 * σ * Real.sqrt E0 := by
                gcongr
                rw [hC18def]; linarith only [hC17]
      -- Lemma A at `(τ, r)` and the `L¹` Hölder bound for `H`
      have hLA : ∫ x in closedBall τ (r / 2), hsNormSq (V.tangentProj x - S.starProjection) ∂V.weight ≤
          144 * (r ^ 2)⁻¹ * Q + 4 * (C18 * σ * Real.sqrt E0) * ∫ x in closedBall τ r, ‖H x‖ ∂V.weight := by
        rw [hQdef]
        exact Submission.ted_lemma_a_tilt_height 1 ℓ le_rfl U hU V H hGMC hmeas hTPF.2.1 τ r
          (C18 * σ * Real.sqrt E0) hr hBτrU (by positivity) S hSdim hhstar
      have hHτ : ∫ x in closedBall τ r, ‖H x‖ ∂V.weight ≤ cω * k := by
        have h1 := hHol1 τ r (2 * (ω * r ^ 1)) (by positivity) hBτσ hμτ
        have h2 := hrpow r σ 1 hr (by linarith only [hrσ, hσ]) one_pos hp1
        have h3 : r ^ (((1 : ℕ) : ℝ) - 1) = 1 := by norm_num
        calc ∫ x in closedBall τ r, ‖H x‖ ∂V.weight
            ≤ (2 * (ω * r ^ 1)) ^ (1 - 1 / p) * σ ^ (1 * (((1 : ℕ) : ℝ) - p) / p) * k := h1
          _ ≤ cω * r ^ (((1 : ℕ) : ℝ) - 1) * k := mul_le_mul_of_nonneg_right h2 hk0
          _ = cω * k := by rw [h3, mul_one]
      have hE : V.tiltExcess τ (r / 2) S ≤
          (r / 2)⁻¹ * (144 * (r ^ 2)⁻¹ * Q + 4 * (C18 * σ * Real.sqrt E0) * (cω * k)) := by
        unfold RectifiableVarifold.tiltExcess
        rw [pow_one]
        gcongr
        exact hLA.trans (by gcongr)
      have hT1 : (r / 2)⁻¹ * (144 * (r ^ 2)⁻¹ * Q) ≤ 288 * X * (16 * t) ^ 2 * E0 := by
        have hQ3 : Q ≤ X * (16 * t) ^ 2 * E0 * r ^ 3 := h20a
        rw [show (r / 2)⁻¹ * (144 * (r ^ 2)⁻¹ * Q) = 288 * (Q / r ^ 3) by field_simp; ring,
          show 288 * X * (16 * t) ^ 2 * E0 = 288 * (X * (16 * t) ^ 2 * E0) by ring]
        gcongr
        rw [div_le_iff₀ (by positivity)]
        exact hQ3
      have hT2 : (r / 2)⁻¹ * (4 * (C18 * σ * Real.sqrt E0) * (cω * k)) ≤
          2 * C18 * cω * (16 * t) ^ 2 * E0 := by
        calc (r / 2)⁻¹ * (4 * (C18 * σ * Real.sqrt E0) * (cω * k))
            ≤ (r / 2)⁻¹ * (4 * (C18 * σ * Real.sqrt E0) * (cω * (Real.sqrt δ * Real.sqrt E0))) := by
              gcongr
          _ = 2 * C18 * cω * (Real.sqrt δ / t) * (Real.sqrt E0 * Real.sqrt E0) := by
              rw [hrdef]; field_simp; ring
          _ = 2 * C18 * cω * (Real.sqrt δ / t) * E0 := by rw [Real.mul_self_sqrt hE0nn]
          _ ≤ 2 * C18 * cω * (16 * t) ^ 2 * E0 := by
              gcongr
              rw [div_le_iff₀ ht]
              calc Real.sqrt δ ≤ t * (16 * t) ^ 2 := hsδt
                _ = (16 * t) ^ 2 * t := by ring
      calc V.tiltExcess τ (r / 2) S
          ≤ (r / 2)⁻¹ * (144 * (r ^ 2)⁻¹ * Q + 4 * (C18 * σ * Real.sqrt E0) * (cω * k)) := hE
        _ = (r / 2)⁻¹ * (144 * (r ^ 2)⁻¹ * Q) +
            (r / 2)⁻¹ * (4 * (C18 * σ * Real.sqrt E0) * (cω * k)) := mul_add _ _ _
        _ ≤ 288 * X * (16 * t) ^ 2 * E0 + 2 * C18 * cω * (16 * t) ^ 2 * E0 := add_le_add hT1 hT2
        _ = (288 * X + 2 * C18 * cω) * (16 * t) ^ 2 * E0 := by ring
        _ ≤ C19 * (16 * t) ^ 2 * E0 := by
            gcongr
            rw [hC19def]
            have : 0 ≤ C21' * (X + cω) := by positivity
            linarith only [this]
  /- Step 7: back to the centre (book (21), (22)); Step 8: conclusion. -/
  refine ⟨S, hSdim, ?_⟩
  have hr2 : r / 2 = 2 * (t * σ) := by rw [hrdef]; ring
  have htσ0 : 0 < t * σ := by positivity
  have hmono := Submission.tdo_tiltExcess_le_of_subset n ℓ U V hmeas 0 τ (t * σ) (r / 2) S htσ0
    (by rw [hr2]; linarith only [htσ0])
    (closedBall_subset_closedBall' (by rw [hr2, dist_zero_left]; linarith only [hτ]))
    ((closedBall_subset_closedBall (by linarith only [hr])).trans hBτrU)
  rw [show r / 2 / (t * σ) = 2 by rw [hr2]; field_simp] at hmono
  calc V.tiltExcess 0 (t * σ) S ≤ 2 ^ n * V.tiltExcess τ (r / 2) S := hmono
    _ ≤ 2 ^ n * (C19 * (16 * t) ^ 2 * E0) := by gcongr
    _ = 2 ^ n * 256 * C19 * t ^ 2 * E0 := by ring
    _ ≤ 2 ^ n * 256 * C19 * t ^ 2 * V.tiltExcessStar H p δ 0 σ T := by gcongr

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
