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
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Covering.Differentiation
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
/-- **Simon Ch. 2, Theorem 1.5 (C¹ approximation of Lipschitz functions).**  A Lipschitz
`f : ℝⁿ → ℝ` agrees with a `C¹` function outside a set of arbitrarily small Lebesgue measure.
Proof, following Simon's printed argument: by Rademacher `f` is differentiable off a Borel null
set; the Whitney quotients `σₖ(x) = sup {|f(x+v) - f(x) - Df(x) v| / |v| : 0 < |v| < 1/(k+1)}`
are lower semicontinuous in `(x, Df(x))`, hence Borel, and tend to `0` wherever `f` is
differentiable; Egorov's theorem on the balls `B(0, J)` with summable tolerances, together with
outer regularity, gives a closed `A` of small complement on whose compact subsets the
first-order Taylor remainder is uniformly small (this also makes `Df` continuous on `A`, so no
separate Lusin step is needed); Whitney's extension theorem (Simon Ch. 2, 1.6), proved inline
with Vitali-selected Whitney balls and a scaled-bump partition of unity, yields `g ∈ C¹` with
`g = f` on `A`. -/
theorem aetp_lipschitz_c1_approximation : ∀ (n : ℕ), 1 ≤ n → ∀ (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x} < ε := by
  intro n _
  -- Whitney's C¹ extension theorem (Simon Ch. 2, Theorem 1.6), in the local uniform form.
  have whitney : ∀ (A : Set (Rn n)) (h : Rn n → ℝ) (D : Rn n → (Rn n →L[ℝ] ℝ)), IsClosed A →
      (∀ a ∈ A, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ (∀ b ∈ A, dist b a < δ → ‖D b - D a‖ ≤ e) ∧
        ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ → |h c - h b - D b (c - b)| ≤ e * ‖c - b‖) →
      ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ ∀ x ∈ A, g x = h x := by
    intro A h D hA hW
    rcases A.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, contDiff_const, fun x hx => hx.elim⟩
    classical
    -- Whitney radius `r x = min 1 (dist (x, A)) / 100`.
    obtain ⟨r, hr⟩ : ∃ r : Rn n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 := ⟨_, fun _ => rfl⟩
    have hr0 : ∀ x, 0 ≤ r x := fun x => by
      rw [hr]; exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
    have hrd : ∀ x, 100 * r x ≤ infDist x A := fun x => by
      rw [hr]; linarith [min_le_right (1 : ℝ) (infDist x A)]
    have hrpos : ∀ x, x ∉ A → 0 < r x := fun x hx => by
      rw [hr]; exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).1 hx)) (by norm_num)
    have hcomp : ∀ x c, dist x c ≤ r x + 10 * r c →
        r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
      have hrlip : ∀ x y, r x ≤ r y + dist x y / 100 := by
        intro x y
        have h1 := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
        simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h1
        rw [hr, hr]
        linarith [(abs_sub_le_iff.1 h1).1]
      intro x c hxc
      have h1 := hrlip x c
      have h2 := hrlip c x
      rw [dist_comm c x] at h2
      have h3 := hr0 x
      have h4 := hr0 c
      exact ⟨by linarith, by linarith, by linarith⟩
    -- Vitali: disjoint balls `B(c, r c)` whose fourfold enlargements cover `Aᶜ`.
    obtain ⟨Cs, hCsA, hCsdisj, hCscov⟩ : ∃ Cs : Set (Rn n), Cs ⊆ Aᶜ ∧
        Cs.PairwiseDisjoint (fun c => ball c (r c)) ∧ ∀ x ∉ A, ∃ c ∈ Cs, dist x c < 4 * r c := by
      have hr1 : ∀ x, r x ≤ 1 / 100 := fun x => by
        rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      obtain ⟨s, hs, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball Aᶜ
        (fun x => x) r (1 / 100) (fun x _ => hr1 x) 4 (by norm_num)
      refine ⟨s, hs, hd, fun x hx => ?_⟩
      obtain ⟨c, hcs, hxc⟩ := hc x hx
      exact ⟨c, hcs, hxc (mem_ball_self (hrpos x hx))⟩
    have hsep : ∀ c ∈ Cs, ∀ c' ∈ Cs, c ≠ c' → r c ≤ dist c c' := by
      intro c hc c' hc' hcc
      by_contra hlt
      exact Set.disjoint_left.1 (hCsdisj hc hc' hcc) (show c' ∈ ball c (r c) by
        rw [mem_ball, dist_comm]; exact not_le.1 hlt) (mem_ball_self (hrpos c' (hCsA hc')))
    -- A uniform packing bound for `1/2`-separated subsets of `B(0, 21)`.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Rn n), s ⊆ closedBall 0 21 →
        s.Pairwise (fun y z => 1 / 2 ≤ dist y z) → s.Finite ∧ s.ncard ≤ N := by
      obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1
        (isCompact_closedBall (0 : Rn n) 21).totallyBounded (1 / 4) (by norm_num)
      refine ⟨t.ncard, fun s hs hs2 => ?_⟩
      have hc : ∀ x : s, ∃ y : t, dist (x : Rn n) y < 1 / 4 := by
        intro x
        obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.1 (hcover (hs x.2))
        exact ⟨⟨y, hyt⟩, hxy⟩
      choose c hc using hc
      have hi : Function.Injective c := by
        intro x y hxy
        by_contra hne
        have hd := hs2 x.2 y.2 (fun h' => hne (Subtype.ext h'))
        have htri := dist_triangle (x : Rn n) (c x) y
        have hxc := hc x
        have hyc := hc y
        rw [← hxy, dist_comm (y : Rn n)] at hyc
        linarith
      have : Finite t := ht.to_subtype
      have : Finite s := Finite.of_injective c hi
      exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
    -- The finite sets `F x` of centres near `x ∉ A`.
    obtain ⟨F, hF⟩ : ∃ F : Rn n → Finset (Rn n), ∀ x, x ∉ A →
        (∀ c, c ∈ F x ↔ c ∈ Cs ∧ dist x c ≤ r x + 10 * r c) ∧ (F x).card ≤ N := by
      have key : ∀ x, x ∉ A → ∃ s : Finset (Rn n),
          (∀ c, c ∈ s ↔ c ∈ Cs ∧ dist x c ≤ r x + 10 * r c) ∧ s.card ≤ N := by
        intro x hx
        have hrx := hrpos x hx
        set T : Set (Rn n) := {c | c ∈ Cs ∧ dist x c ≤ r x + 10 * r c} with hT
        obtain ⟨φ, hφ⟩ : ∃ φ : Rn n → Rn n, ∀ c, φ c = (r x)⁻¹ • (c - x) := ⟨_, fun _ => rfl⟩
        have hφi : Function.Injective φ := by
          intro c d hcd
          rw [hφ, hφ] at hcd
          have := congrArg (fun z => r x • z) hcd
          simpa [smul_smul, hrx.ne'] using this
        have hnφ : ∀ c d, dist (φ c) (φ d) = dist c d / r x := by
          intro c d
          rw [hφ, hφ, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.2 hrx.le), ← dist_eq_norm, inv_mul_eq_div]
        have hsub : φ '' T ⊆ closedBall 0 21 := by
          rintro _ ⟨c, hc, rfl⟩
          have h0 : φ x = 0 := by rw [hφ, sub_self, smul_zero]
          rw [mem_closedBall, ← h0, hnφ, div_le_iff₀ hrx, dist_comm]
          exact (hcomp x c hc.2).2.2
        have hsep' : (φ '' T).Pairwise (fun y z => 1 / 2 ≤ dist y z) := by
          rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
          have h1 := hsep c hc.1 d hd.1 (fun h' => hcd (congrArg φ h'))
          have h2 := (hcomp x c hc.2).1
          rw [hnφ, le_div_iff₀ hrx]
          linarith
        obtain ⟨hfin, hcard⟩ := hN (φ '' T) hsub hsep'
        have hTfin : T.Finite := hfin.of_finite_image hφi.injOn
        refine ⟨hTfin.toFinset, fun c => hTfin.mem_toFinset, ?_⟩
        rw [← Set.ncard_eq_toFinset_card T hTfin, ← Set.ncard_image_of_injective T hφi]
        exact hcard
      choose! F hF using key
      exact ⟨F, hF⟩
    -- A fixed bump `β`, equal to `1` on `B(0, 4)` and to `0` off `B(0, 8)`.
    obtain ⟨β, hβ0, hβ1, hβone, hβzero, hβs, L, hL⟩ : ∃ β : Rn n → ℝ, (∀ y, 0 ≤ β y) ∧
        (∀ y, β y ≤ 1) ∧ (∀ y, ‖y‖ ≤ 4 → β y = 1) ∧ (∀ y, 8 ≤ ‖y‖ → β y = 0) ∧
        ContDiff ℝ 1 β ∧ ∃ L : ℝ≥0, LipschitzWith L β := by
      let b : ContDiffBump (0 : Rn n) := ⟨4, 8, by norm_num, by norm_num⟩
      refine ⟨b, fun y => b.nonneg, fun y => b.le_one, fun y hy => b.one_of_mem_closedBall ?_,
        fun y hy => Function.notMem_support.1 ?_, b.contDiff (n := 1),
        ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport (b.contDiff (n := 1))
          one_ne_zero⟩
      · rw [mem_closedBall, dist_zero_right]; exact hy
      · rw [b.support_eq, mem_ball, dist_zero_right]; exact not_lt.2 hy
    -- The rescaled bumps `ψ c y = β ((y - c) / r c)`.
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Rn n → Rn n → ℝ, ∀ c y, ψ c y = β ((r c)⁻¹ • (y - c)) :=
      ⟨_, fun _ _ => rfl⟩
    have hnsc : ∀ c y, 0 < r c → ‖(r c)⁻¹ • (y - c)‖ = dist y c / r c := by
      intro c y hc
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le), dist_eq_norm, inv_mul_eq_div]
    have hψ0 : ∀ c y, 0 ≤ ψ c y := fun c y => by rw [hψ]; exact hβ0 _
    have hψone : ∀ c y, 0 < r c → dist y c ≤ 4 * r c → ψ c y = 1 := by
      intro c y hc hy; rw [hψ]; apply hβone; rw [hnsc c y hc, div_le_iff₀ hc]; exact hy
    have hψzero : ∀ c y, 0 < r c → 8 * r c ≤ dist y c → ψ c y = 0 := by
      intro c y hc hy; rw [hψ]; apply hβzero; rw [hnsc c y hc, le_div_iff₀ hc]; exact hy
    have hψs : ∀ c, ContDiff ℝ 1 (ψ c) := by
      intro c
      rw [show ψ c = fun y => β ((r c)⁻¹ • (y - c)) from funext (hψ c)]
      exact hβs.comp ((contDiff_id.sub contDiff_const).const_smul _)
    have hψd : ∀ c y, 0 < r c → ‖fderiv ℝ (ψ c) y‖ ≤ L / r c := by
      intro c y hc
      have hlip : LipschitzWith (L * (Real.toNNReal (r c))⁻¹) (ψ c) := by
        refine LipschitzWith.of_dist_le_mul fun y z => ?_
        rw [hψ, hψ, NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hc.le]
        refine (hL.dist_le_mul _ _).trans (le_of_eq ?_)
        rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 hc.le), dist_eq_norm, mul_assoc]
      have := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := y)
      rwa [NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hc.le, ← div_eq_mul_inv] at this
    -- The locally finite sum `S = ∑ c ∈ Cs, ψ c ≥ 1` on `Aᶜ`.
    obtain ⟨S, hS⟩ : ∃ S : Rn n → ℝ, ∀ y, S y = ∑ᶠ c ∈ Cs, ψ c y := ⟨_, fun _ => rfl⟩
    have hψF : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c ∈ Cs, c ∉ F x → ψ c y = 0 := by
      intro x hx y hy c hc hcF
      apply hψzero c y (hrpos c (hCsA hc))
      have h1 : ¬ dist x c ≤ r x + 10 * r c := fun h' => hcF (((hF x hx).1 c).2 ⟨hc, h'⟩)
      have h2 := dist_triangle x y c
      rw [dist_comm x y] at h2
      have h3 := hr0 c
      linarith
    have hSloc : ∀ x, x ∉ A → ∀ y, dist y x < r x → S y = ∑ c ∈ F x, ψ c y := by
      intro x hx y hy
      rw [hS]
      apply finsum_mem_eq_sum_of_inter_support_eq
      ext c
      simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
      exact ⟨fun hc => ⟨Classical.byContradiction fun h' => hc.2 (hψF x hx y hy c hc.1 h'), hc.2⟩,
        fun hc => ⟨(((hF x hx).1 c).1 hc.1).1, hc.2⟩⟩
    have hS1 : ∀ x, x ∉ A → 1 ≤ S x := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := hCscov x hx
      have hcF : c ∈ F x := ((hF x hx).1 c).2 ⟨hc, by linarith [hr0 x, hr0 c]⟩
      rw [hSloc x hx x (by rw [dist_self]; exact hrpos x hx)]
      calc (1 : ℝ) = ψ c x := (hψone c x (hrpos c (hCsA hc)) hxc.le).symm
        _ ≤ ∑ c ∈ F x, ψ c x := Finset.single_le_sum (fun c _ => hψ0 c x) hcF
    have hSc : ∀ x, x ∉ A → ContDiffAt ℝ 1 S x := by
      intro x hx
      refine (ContDiff.contDiffAt (ContDiff.sum (s := F x) fun c _ => hψs c)).congr_of_eventuallyEq ?_
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hSloc x hx y hy
    have hnotA : ∀ x, x ∉ A → ∀ y, dist y x < r x → y ∉ A := by
      intro x hx y hy hyA
      have h1 := infDist_le_dist_of_mem (x := x) hyA
      rw [dist_comm] at h1
      linarith [hrd x, hr0 x]
    -- The partition of unity `φ c = ψ c / S` on `Aᶜ`.
    obtain ⟨φ, hφ⟩ : ∃ φ : Rn n → Rn n → ℝ, ∀ c y, φ c y = ψ c y / S y := ⟨_, fun _ _ => rfl⟩
    have hφcd : ∀ c x, x ∉ A → ContDiffAt ℝ 1 (φ c) x := by
      intro c x hx
      rw [show φ c = ψ c / S from funext (hφ c)]
      exact (hψs c).contDiffAt.div (hSc x hx) (ne_of_gt (lt_of_lt_of_le one_pos (hS1 x hx)))
    have hφ0 : ∀ c y, y ∉ A → 0 ≤ φ c y := fun c y hy => by
      rw [hφ]; exact div_nonneg (hψ0 c y) (le_trans zero_le_one (hS1 y hy))
    have hφsum : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∑ c ∈ F x, φ c y = 1 := by
      intro x hx y hy
      simp only [hφ]
      rw [← Finset.sum_div, ← hSloc x hx y hy]
      exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (hS1 y (hnotA x hx y hy))))
    have hφF : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c ∈ Cs, c ∉ F x → φ c y = 0 := by
      intro x hx y hy c hc hcF
      rw [hφ, hψF x hx y hy c hc hcF, zero_div]
    have hφdsum : ∀ x, x ∉ A → ∑ c ∈ F x, fderiv ℝ (φ c) x = 0 := by
      intro x hx
      have heq : (fun y => ∑ c ∈ F x, φ c y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
        exact hφsum x hx y hy
      have h1 := heq.fderiv_eq (𝕜 := ℝ)
      rwa [fderiv_fun_const, Pi.zero_apply, fderiv_fun_sum fun c _ =>
        (hφcd c x hx).differentiableAt one_ne_zero] at h1
    -- `‖Dφ_c‖ ≤ ‖Dψ_c‖ + ‖DS‖` off `A` (quotient rule, `S ≥ 1`, `0 ≤ ψ_c ≤ 1`).
    have hφd : ∀ c x, x ∉ A → ‖fderiv ℝ (φ c) x‖ ≤ ‖fderiv ℝ (ψ c) x‖ + ‖fderiv ℝ S x‖ := by
      intro c x hx
      have hS1x := hS1 x hx
      have hSpos : 0 < S x := lt_of_lt_of_le one_pos hS1x
      have hb := ((hψs c).differentiable one_ne_zero x).hasFDerivAt
      have hd := ((hSc x hx).differentiableAt one_ne_zero).hasFDerivAt
      have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
      have hder : fderiv ℝ (φ c) x =
          ψ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (ψ c) x := by
        rw [show φ c = fun y => ψ c y * ((fun t : ℝ => t⁻¹) ∘ S) y from
          funext fun y => by rw [hφ, div_eq_mul_inv]; rfl]
        exact (hb.fun_mul hi).fderiv
      have hp0 := hψ0 c x
      have hp1 : ψ c x ≤ 1 := by rw [hψ]; exact hβ1 _
      have hsi : (S x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS1x
      have hsi2 : (S x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hS1x)
      rw [hder]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, norm_smul, norm_neg, Real.norm_of_nonneg hp0,
        Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), add_comm]
      exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hsi)
        (mul_le_of_le_one_left (by positivity) hp1 |>.trans (mul_le_of_le_one_left (norm_nonneg _) hsi2))
    obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧
        ∀ x, x ∉ A → ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ M / r x := by
      refine ⟨(N + 1) * (N * (2 * L)), by positivity, fun x hx => ?_⟩
      have hrx := hrpos x hx
      have hb : ∀ c ∈ F x, ‖fderiv ℝ (ψ c) x‖ ≤ 2 * L / r x := by
        intro c hc
        have hc' := ((hF x hx).1 c).1 hc
        have hrc := hrpos c (hCsA hc'.1)
        refine (hψd c x hrc).trans ?_
        rw [div_le_div_iff₀ hrc hrx]
        calc (L : ℝ) * r x ≤ L * (2 * r c) :=
              mul_le_mul_of_nonneg_left (by linarith [(hcomp x c hc'.2).1]) L.2
          _ = 2 * L * r c := by ring
      have hN' : ((F x).card : ℝ) ≤ N := by exact_mod_cast (hF x hx).2
      have hb0 : (0 : ℝ) ≤ 2 * L / r x := div_nonneg (by positivity) hrx.le
      have hSd : ‖fderiv ℝ S x‖ ≤ N * (2 * L / r x) := by
        have heq : S =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, ψ c y := by
          filter_upwards [ball_mem_nhds x hrx] with y hy
          exact hSloc x hx y hy
        rw [heq.fderiv_eq, fderiv_fun_sum fun c _ => (hψs c).differentiable one_ne_zero x]
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hb).trans ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hN' hb0
      calc ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ ∑ c ∈ F x, (2 * L / r x + N * (2 * L / r x)) :=
            Finset.sum_le_sum fun c hc => (hφd c x hx).trans (add_le_add (hb c hc) hSd)
        _ = (F x).card * ((N + 1) * (2 * L / r x)) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ N * ((N + 1) * (2 * L / r x)) := mul_le_mul_of_nonneg_right hN' (by positivity)
        _ = (N + 1) * (N * (2 * L)) / r x := by ring
    -- Nearest-point anchors and the affine jets `Q a y = h a + D a (y - a)`.
    obtain ⟨anc, hancA, hancd⟩ : ∃ anc : Rn n → Rn n, (∀ x, anc x ∈ A) ∧
        ∀ x, dist x (anc x) = infDist x A := by
      choose anc hanc using fun x => hA.exists_infDist_eq_dist hne x
      exact ⟨anc, fun x => (hanc x).1, fun x => (hanc x).2.symm⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : Rn n → Rn n → ℝ, ∀ a y, Q a y = h a + (D a y - D a a) :=
      ⟨_, fun _ _ => rfl⟩
    have hQs : ∀ a, ContDiff ℝ 1 (Q a) := by
      intro a
      rw [show Q a = fun y => h a + (D a y - D a a) from funext (hQ a)]
      exact contDiff_const.add ((D a).contDiff.sub contDiff_const)
    have hQd : ∀ a y, HasFDerivAt (Q a) (D a) y := by
      intro a y
      rw [show Q a = fun y => h a + (D a y - D a a) from funext (hQ a)]
      exact ((D a).hasFDerivAt.sub_const _).const_add _
    have hQsub : ∀ a b y,
        |Q b y - Q a y| ≤ |h b - h a - D a (b - a)| + ‖D b - D a‖ * ‖y - b‖ := by
      intro a b y
      have e1 : Q b y - Q a y = (h b - h a - D a (b - a)) + (D b - D a) (y - b) := by
        rw [hQ, hQ]; simp only [map_sub, sub_apply]; ring
      rw [e1]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      have := (D b - D a).le_opNorm (y - b)
      rwa [Real.norm_eq_abs] at this
    have hancF : ∀ x, x ∉ A → ∀ c ∈ F x, dist x (anc c) ≤ 2 * infDist x A := by
      intro x hx c hc
      have h1 := (hcomp x c (((hF x hx).1 c).1 hc).2).2.2
      have h2 := hrd x
      have h3 := infDist_le_infDist_add_dist (s := A) (x := c) (y := x)
      have h4 := dist_triangle x c (anc c)
      rw [hancd c] at h4
      rw [dist_comm c x] at h3
      linarith [hr0 x]
    have hancP : ∀ x, x ∉ A → ∀ a ∈ A, ∀ c ∈ F x, dist (anc c) a ≤ 3 * dist x a := by
      intro x hx a ha c hc
      have h1 := hancF x hx c hc
      have h2 := infDist_le_dist_of_mem (x := x) ha
      have h3 := dist_triangle (anc c) x a
      rw [dist_comm (anc c) x] at h3
      linarith
    -- The Whitney extension `g`.
    obtain ⟨g, hg⟩ : ∃ g : Rn n → ℝ, ∀ y,
        g y = if y ∈ A then h y else ∑ᶠ c ∈ Cs, φ c y * Q (anc c) y := ⟨_, fun _ => rfl⟩
    have hgA : ∀ a ∈ A, g a = h a := fun a ha => by rw [hg, ite_eq_left ha]
    have hgloc : ∀ x, x ∉ A → ∀ y, dist y x < r x → g y = ∑ c ∈ F x, φ c y * Q (anc c) y := by
      intro x hx y hy
      rw [hg, ite_eq_right (hnotA x hx y hy)]
      apply finsum_mem_eq_sum_of_inter_support_eq
      ext c
      simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
      refine ⟨fun hc => ⟨Classical.byContradiction fun h' => hc.2 ?_, hc.2⟩,
        fun hc => ⟨(((hF x hx).1 c).1 hc.1).1, hc.2⟩⟩
      rw [hφF x hx y hy c hc.1 h', zero_mul]
    have hgev : ∀ x, x ∉ A → g =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, φ c y * Q (anc c) y := by
      intro x hx
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hgloc x hx y hy
    have hgd : ∀ x, x ∉ A → HasFDerivAt g
        (∑ c ∈ F x, (φ c x • D (anc c) + Q (anc c) x • fderiv ℝ (φ c) x)) x := by
      intro x hx
      refine HasFDerivAt.congr_of_eventuallyEq ?_ (hgev x hx)
      exact HasFDerivAt.fun_sum fun c _ =>
        ((hφcd c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (hQd (anc c) x)
    have hgcd : ∀ x, x ∉ A → ContDiffAt ℝ 1 g x := by
      intro x hx
      refine ContDiffAt.congr_of_eventuallyEq ?_ (hgev x hx)
      exact ContDiffAt.sum fun c _ => (hφcd c x hx).mul (hQs (anc c)).contDiffAt
    -- `g` has derivative `D a` at each `a ∈ A`.
    have hgdA : ∀ a ∈ A, HasFDerivAt g (D a) a := by
      intro a ha
      refine HasFDerivAt.of_isLittleO (Asymptotics.IsLittleO.of_bound fun e he => ?_)
      obtain ⟨δ, hδ, -, hDd, hrem⟩ := hW a ha (e / 5) (by positivity)
      have haa : dist a a < δ := by rw [dist_self]; exact hδ
      filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
      have hxa : dist x a < δ / 4 := hx
      rw [hgA a ha]
      by_cases hxA : x ∈ A
      · rw [hgA x hxA, Real.norm_eq_abs]
        exact (hrem a ha haa x hxA (by linarith)).trans
          (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      · have hx0 : dist x x < r x := by rw [dist_self]; exact hrpos x hxA
        have e1 : g x - h a - D a (x - a) = ∑ c ∈ F x, φ c x * (Q (anc c) x - Q a x) := by
          rw [hgloc x hxA x hx0]
          simp only [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hφsum x hxA x hx0, one_mul, hQ a x,
            map_sub]
          ring
        rw [e1, Real.norm_eq_abs]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ c ∈ F x, |φ c x * (Q (anc c) x - Q a x)| ≤ ∑ c ∈ F x, φ c x * (e * ‖x - a‖) := by
              refine Finset.sum_le_sum fun c hc => ?_
              rw [abs_mul, abs_of_nonneg (hφ0 c x hxA)]
              refine mul_le_mul_of_nonneg_left ?_ (hφ0 c x hxA)
              have hba := hancP x hxA a ha c hc
              have hxb : dist x (anc c) ≤ 2 * dist x a :=
                (hancF x hxA c hc).trans (by linarith [infDist_le_dist_of_mem (x := x) ha])
              have hbaδ : dist (anc c) a < δ := by linarith
              have h1 := hrem a ha haa (anc c) (hancA c) hbaδ
              have h2 := hDd (anc c) (hancA c) hbaδ
              rw [dist_eq_norm] at hba hxb
              refine (hQsub a (anc c) x).trans ?_
              calc |h (anc c) - h a - D a (anc c - a)| + ‖D (anc c) - D a‖ * ‖x - anc c‖
                  ≤ e / 5 * ‖anc c - a‖ + e / 5 * ‖x - anc c‖ :=
                    add_le_add h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
                _ ≤ e / 5 * (3 * ‖x - a‖) + e / 5 * (2 * ‖x - a‖) :=
                    add_le_add (mul_le_mul_of_nonneg_left hba (by positivity))
                      (mul_le_mul_of_nonneg_left hxb (by positivity))
                _ = e * ‖x - a‖ := by ring
          _ = e * ‖x - a‖ := by rw [← Finset.sum_mul, hφsum x hxA x hx0, one_mul]
    -- `Dg` is continuous at each `a ∈ A`.
    have hgcA : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
      intro a ha
      rw [Metric.continuousAt_iff]
      intro e he
      obtain ⟨δ, hδ, hδ1, hDd, hrem⟩ := hW a ha (e / (2 * (1 + 700 * M))) (by positivity)
      set η := e / (2 * (1 + 700 * M)) with hη
      have hη0 : 0 < η := by positivity
      have hηM : η * (1 + 700 * M) = e / 2 := by rw [hη]; field_simp
      have hηM' := mul_nonneg hη0.le hM0
      refine ⟨δ / 4, by positivity, fun x hxa => ?_⟩
      rw [(hgdA a ha).fderiv, dist_eq_norm]
      by_cases hxA : x ∈ A
      · rw [(hgdA x hxA).fderiv]
        exact (hDd x hxA (by linarith)).trans_lt (by linarith)
      · have hrx := hrpos x hxA
        have hx0 : dist x x < r x := by rw [dist_self]; exact hrx
        have hbA : anc x ∈ A := hancA x
        have hdxa : infDist x A ≤ dist x a := infDist_le_dist_of_mem ha
        have hba : dist (anc x) a < δ := by
          have := dist_triangle (anc x) x a
          rw [dist_comm (anc x) x, hancd x] at this
          linarith
        have hd1 : infDist x A = 100 * r x := by
          rw [hr, min_eq_right (by linarith : infDist x A ≤ 1)]
          ring
        have hDb := hDd (anc x) hbA hba
        have e1 : (∑ c ∈ F x, (φ c x • D (anc c) + Q (anc c) x • fderiv ℝ (φ c) x)) - D a =
            (∑ c ∈ F x, φ c x • (D (anc c) - D a)) +
              ∑ c ∈ F x, (Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x := by
          simp_rw [smul_sub, sub_smul]
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            ← Finset.sum_smul, ← Finset.smul_sum, hφsum x hxA x hx0, hφdsum x hxA, one_smul,
            smul_zero, sub_zero]
          abel
        rw [(hgd x hxA).fderiv, e1]
        have hT1 : ‖∑ c ∈ F x, φ c x • (D (anc c) - D a)‖ ≤ η := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ c ∈ F x, ‖φ c x • (D (anc c) - D a)‖ ≤ ∑ c ∈ F x, φ c x * η :=
                Finset.sum_le_sum fun c hc => by
                  rw [norm_smul, Real.norm_of_nonneg (hφ0 c x hxA)]
                  exact mul_le_mul_of_nonneg_left
                    (hDd (anc c) (hancA c) (by linarith [hancP x hxA a ha c hc])) (hφ0 c x hxA)
            _ = η := by rw [← Finset.sum_mul, hφsum x hxA x hx0, one_mul]
        have hT2 : ‖∑ c ∈ F x, (Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x‖ ≤
            700 * η * r x * (M / r x) := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ c ∈ F x, ‖(Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x‖
              ≤ ∑ c ∈ F x, 700 * η * r x * ‖fderiv ℝ (φ c) x‖ :=
                Finset.sum_le_sum fun c hc => by
                  rw [norm_smul, Real.norm_eq_abs]
                  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                  have hcaδ : dist (anc c) a < δ := by linarith [hancP x hxA a ha c hc]
                  have hxc := hancF x hxA c hc
                  have hcb : dist (anc c) (anc x) ≤ 3 * infDist x A := by
                    have := dist_triangle (anc c) x (anc x)
                    rw [dist_comm (anc c) x, hancd x] at this
                    linarith
                  have h1 := hrem (anc x) hbA hba (anc c) (hancA c) hcaδ
                  have h2 : ‖D (anc c) - D (anc x)‖ ≤ 2 * η := by
                    rw [← sub_sub_sub_cancel_right (D (anc c)) (D (anc x)) (D a)]
                    exact (norm_sub_le _ _).trans (by linarith [hDd (anc c) (hancA c) hcaδ])
                  rw [dist_eq_norm] at hcb hxc
                  refine (hQsub (anc x) (anc c) x).trans ?_
                  calc |h (anc c) - h (anc x) - D (anc x) (anc c - anc x)| +
                        ‖D (anc c) - D (anc x)‖ * ‖x - anc c‖
                      ≤ η * ‖anc c - anc x‖ + 2 * η * ‖x - anc c‖ :=
                        add_le_add h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
                    _ ≤ η * (3 * infDist x A) + 2 * η * (2 * infDist x A) :=
                        add_le_add (mul_le_mul_of_nonneg_left hcb hη0.le)
                          (mul_le_mul_of_nonneg_left hxc (by positivity))
                    _ = 700 * η * r x := by rw [hd1]; ring
            _ = 700 * η * r x * ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ := by rw [Finset.mul_sum]
            _ ≤ 700 * η * r x * (M / r x) :=
                mul_le_mul_of_nonneg_left (hM x hxA) (mul_nonneg (by positivity) hrx.le)
        have hfin : 700 * η * r x * (M / r x) = 700 * (η * M) := by field_simp
        rw [hfin] at hT2
        exact (norm_add_le _ _).trans_lt (by linarith)
    refine ⟨g, contDiff_one_iff_fderiv.2 ⟨fun x => ?_, continuous_iff_continuousAt.2 fun x => ?_⟩,
      hgA⟩
    · by_cases hx : x ∈ A
      · exact (hgdA x hx).differentiableAt
      · exact (hgd x hx).differentiableAt
    · by_cases hx : x ∈ A
      · exact hgcA x hx
      · exact (hgcd x hx).continuousAt_fderiv one_ne_zero
  intro f K hf ε hε
  have hfc : Continuous f := hf.continuous
  -- Rademacher: `f` is differentiable off a Borel null set.
  have hBm : MeasurableSet {x | DifferentiableAt ℝ f x} := measurableSet_of_differentiableAt ℝ f
  have hB0 : volume {x | DifferentiableAt ℝ f x}ᶜ = 0 := by
    have h1 := hf.ae_differentiableAt (μ := (volume : Measure (Rn n)))
    rwa [ae_iff, ← Set.compl_ofPred] at h1
  -- Whitney quotients `σ k (x, L) = sup {|f (x + v) - f x - L v| / |v| : 0 < |v| < 1/(k+1)}`.
  obtain ⟨σ, hσ0, hσle, hσge, hσlsc⟩ : ∃ σ : ℕ → Rn n × (Rn n →L[ℝ] ℝ) → ℝ,
      (∀ k p, 0 ≤ σ k p) ∧
      (∀ (k : ℕ) p (v : Rn n), 0 < ‖v‖ → ‖v‖ < 1 / ((k : ℝ) + 1) →
        |f (p.1 + v) - f p.1 - p.2 v| ≤ σ k p * ‖v‖) ∧
      (∀ (k : ℕ) p (t : ℝ), 0 ≤ t → (∀ v : Rn n, 0 < ‖v‖ → ‖v‖ < 1 / ((k : ℝ) + 1) →
        |f (p.1 + v) - f p.1 - p.2 v| ≤ t * ‖v‖) → σ k p ≤ t) ∧
      ∀ k, LowerSemicontinuous (σ k) := by
    have hbdd : ∀ (k : ℕ) (p : Rn n × (Rn n →L[ℝ] ℝ)), BddAbove (range fun v :
        {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)} =>
          |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖) := by
      intro k p
      refine ⟨K + ‖p.2‖, ?_⟩
      rintro _ ⟨v, rfl⟩
      rw [div_le_iff₀ v.2.1]
      have h1 := hf.dist_le_mul (p.1 + v) p.1
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at h1
      have h2 := p.2.le_opNorm v
      rw [Real.norm_eq_abs] at h2
      calc |f (p.1 + v) - f p.1 - p.2 v| ≤ |f (p.1 + v) - f p.1| + |p.2 v| := abs_sub _ _
        _ ≤ K * ‖(v : Rn n)‖ + ‖p.2‖ * ‖(v : Rn n)‖ := add_le_add h1 h2
        _ = (K + ‖p.2‖) * ‖(v : Rn n)‖ := by ring
    refine ⟨fun k p => ⨆ v : {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)},
      |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖, fun k p => Real.iSup_nonneg fun v =>
        div_nonneg (abs_nonneg _) (norm_nonneg _), fun k p v hv0 hv1 => ?_,
      fun k p t ht hle => Real.iSup_le (fun v => ?_) ht, fun k => ?_⟩
    · rw [← div_le_iff₀ hv0]
      exact le_ciSup (f := fun v : {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)} =>
        |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖) (hbdd k p) ⟨v, hv0, hv1⟩
    · rw [div_le_iff₀ v.2.1]
      exact hle v v.2.1 v.2.2
    · refine lowerSemicontinuous_ciSup (hbdd k) fun v => Continuous.lowerSemicontinuous ?_
      exact (((hfc.comp (continuous_fst.add continuous_const)).sub (hfc.comp continuous_fst)).sub
        (continuous_snd.clm_apply continuous_const)).abs.div_const _
  have hσm : ∀ k, Measurable fun x => σ k (x, fderiv ℝ f x) := fun k =>
    (hσlsc k).measurable.comp (measurable_id.prodMk (measurable_fderiv ℝ f))
  have hσlim : ∀ x, DifferentiableAt ℝ f x →
      Tendsto (fun k => σ k (x, fderiv ℝ f x)) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro t ht
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1
      (Asymptotics.isLittleO_iff.1 hx.hasFDerivAt.isLittleO (half_pos ht))
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hρ
    refine ⟨k₀, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hσ0 k _)]
    refine lt_of_le_of_lt (hσge k _ (t / 2) (by positivity) fun v hv0 hv1 => ?_) (half_lt_self ht)
    have hk' : 1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    have h1 := @hball (x + v) (by rw [dist_eq_norm, add_sub_cancel_left]; linarith)
    rwa [add_sub_cancel_left, Real.norm_eq_abs] at h1
  -- Egorov on the balls `B(0, J)`, with summable tolerances.
  obtain ⟨δs, hδs0, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  have hEg : ∀ J : ℕ, ∃ t ⊆ ball (0 : Rn n) J ∩ {x | DifferentiableAt ℝ f x}, MeasurableSet t ∧
      volume t ≤ δs J ∧ TendstoUniformlyOn (fun k x => σ k (x, fderiv ℝ f x)) (fun _ => (0 : ℝ))
        atTop ((ball (0 : Rn n) J ∩ {x | DifferentiableAt ℝ f x}) \ t) := fun J =>
    tendstoUniformlyOn_of_ae_tendsto (fun k => (hσm k).stronglyMeasurable) stronglyMeasurable_const
      (measurableSet_ball.inter hBm) ((measure_mono inter_subset_left).trans_lt
        measure_ball_lt_top).ne (Filter.Eventually.of_forall fun x hx => hσlim x hx.2)
      (by exact_mod_cast hδs0 J)
  choose t htsub _ htle htu using hEg
  -- An open `U` of measure `< ε` containing the bad set; `A = Uᶜ`.
  have hZ : volume ({x | DifferentiableAt ℝ f x}ᶜ ∪ ⋃ J, t J) < ε := by
    calc volume ({x | DifferentiableAt ℝ f x}ᶜ ∪ ⋃ J, t J)
        ≤ volume {x | DifferentiableAt ℝ f x}ᶜ + volume (⋃ J, t J) := measure_union_le _ _
      _ ≤ 0 + ∑' J, (δs J : ℝ≥0∞) :=
          add_le_add hB0.le ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum htle))
      _ < ε := by rw [zero_add]; exact hδsum
  obtain ⟨U, hZU, hUo, hUε⟩ := Set.exists_isOpen_lt_of_lt _ _ hZ
  -- Uniform first-order Taylor estimate on compact subsets of `Uᶜ`.
  have hunif : ∀ Q ⊆ Uᶜ, IsCompact Q → ∀ s : ℝ, 0 < s → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ Q, ∀ v : Rn n, ‖v‖ < ρ → |f (x + v) - f x - fderiv ℝ f x v| ≤ s * ‖v‖ := by
    intro Q hQU hQ s hs
    obtain ⟨R, hR⟩ := hQ.isBounded.subset_ball (0 : Rn n)
    obtain ⟨J, hJ⟩ := exists_nat_gt R
    obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.1 (htu J) s hs).exists
    refine ⟨1 / ((k : ℝ) + 1), by positivity, fun x hx v hv => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    have hxU : x ∉ U := hQU hx
    have hxJ : x ∈ (ball (0 : Rn n) J ∩ {x | DifferentiableAt ℝ f x}) \ t J :=
      ⟨⟨ball_subset_ball hJ.le (hR hx), Classical.byContradiction fun h' =>
        hxU (hZU (Or.inl h'))⟩, fun h' => hxU (hZU (Or.inr (mem_iUnion.2 ⟨J, h'⟩)))⟩
    have h1 := hk x hxJ
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hσ0 _ _)] at h1
    exact (hσle k (x, fderiv ℝ f x) v (norm_pos_iff.2 hv0) hv).trans
      (mul_le_mul_of_nonneg_right h1.le (norm_nonneg _))
  -- Whitney's hypothesis on `Uᶜ`, including continuity of `Df` there.
  have hW2 : ∀ a ∈ Uᶜ, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ Uᶜ, dist b a < δ → ‖fderiv ℝ f b - fderiv ℝ f a‖ ≤ e) ∧
      ∀ b ∈ Uᶜ, dist b a < δ → ∀ c ∈ Uᶜ, dist c a < δ →
        |f c - f b - fderiv ℝ f b (c - b)| ≤ e * ‖c - b‖ := by
    intro a ha e he
    obtain ⟨ρ, hρ, hρU⟩ := hunif (Uᶜ ∩ closedBall a 1) inter_subset_left
      ((isCompact_closedBall a 1).inter_left hUo.isClosed_compl) (e / 4) (by positivity)
    have hK : (0 : ℝ) ≤ K := K.2
    set δ := min (min 1 (ρ / 2)) (e * ρ / (8 * K + 1)) with hδ
    have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
    have hδρ : δ ≤ ρ / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hδe : δ ≤ e * ρ / (8 * K + 1) := min_le_right _ _
    have haQ : a ∈ Uᶜ ∩ closedBall a 1 := ⟨ha, mem_closedBall_self zero_le_one⟩
    refine ⟨δ, lt_min (lt_min one_pos (half_pos hρ)) (by positivity), hδ1, fun b hb hba => ?_,
      fun b hb hba c hc hca => ?_⟩
    · have hbQ : b ∈ Uᶜ ∩ closedBall a 1 := ⟨hb, mem_closedBall.2 (by linarith)⟩
      have hd : dist b a * (8 * K + 1) ≤ e * ρ := by
        rw [← le_div_iff₀ (by positivity)]; linarith
      refine ContinuousLinearMap.opNorm_le_of_shell (c := (2 : ℝ)) hρ he.le
        (by norm_num) fun w hw1 hw2 => ?_
      rw [Real.norm_two] at hw1
      have h1 := hρU b hbQ w hw2
      have h2 := hρU a haQ w hw2
      have h3 := hf.dist_le_mul (b + w) (a + w)
      have h4 := hf.dist_le_mul b a
      rw [Real.dist_eq, dist_add_right] at h3
      rw [Real.dist_eq] at h4
      have h5 : e * ρ ≤ e * (2 * ‖w‖) := mul_le_mul_of_nonneg_left (by linarith) he.le
      have h6 : 0 ≤ dist b a := dist_nonneg
      rw [sub_apply, Real.norm_eq_abs]
      have e1 : fderiv ℝ f b w - fderiv ℝ f a w = (f (b + w) - f (a + w)) - (f b - f a) -
          (f (b + w) - f b - fderiv ℝ f b w) + (f (a + w) - f a - fderiv ℝ f a w) := by ring
      rw [e1]
      have := abs_add_le ((f (b + w) - f (a + w)) - (f b - f a) -
          (f (b + w) - f b - fderiv ℝ f b w)) (f (a + w) - f a - fderiv ℝ f a w)
      have := abs_sub ((f (b + w) - f (a + w)) - (f b - f a)) (f (b + w) - f b - fderiv ℝ f b w)
      have := abs_sub (f (b + w) - f (a + w)) (f b - f a)
      linarith
    · have hbQ : b ∈ Uᶜ ∩ closedBall a 1 := ⟨hb, mem_closedBall.2 (by linarith)⟩
      have hcb : ‖c - b‖ < ρ := by
        have := dist_triangle c a b
        rw [dist_comm a b, dist_eq_norm] at this
        linarith
      have h1 := hρU b hbQ (c - b) hcb
      rw [add_sub_cancel] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  obtain ⟨g, hg, hgA⟩ := whitney Uᶜ f (fderiv ℝ f) hUo.isClosed_compl hW2
  refine ⟨g, hg, (measure_mono fun x hx => ?_).trans_lt hUε⟩
  by_contra hxU
  exact hx (hgA x hxU).symm

/-- **Countably rectifiable sets are covered by `C¹` pieces with injective differential** (Simon
Ch. 3, proof of Lemma 1.2, "only if").  If `M ⊆ ℝ^{n+ℓ}` is countably `n`-rectifiable, then up to a
Borel `Hⁿ`-null set `Z₀` it is covered by countably many images `G_k(B̆_{r_k}(c_k))` of open balls
under `C¹` maps `G_k : ℝⁿ → ℝ^{n+ℓ}` whose differential is injective on the ball and which satisfy
the lower Lipschitz bound `σ_k |b₁ - b₂| ≤ |G_k b₁ - G_k b₂|` there.
Proof: approximate the coordinates of the Lipschitz maps `F_j` of Definition 1.1 by `C¹` functions
(Simon Ch. 2, Theorem 1.5, `aetp_lipschitz_c1_approximation`); the set where `F_j` differs from all
approximations is Lebesgue-null, so its image is `Hⁿ`-null.  The image of the critical set of a `C¹`
map `G : ℝⁿ → ℝ^{n+ℓ}` is `Hⁿ`-null: on a piece where `G` is `η`-close to a non-injective linear `A`
with kernel vector `u`, `G` factors through the linear map `Θ = id - (1 - η) u ⊗ u` (which has
determinant `η`) via an `(‖A‖ + 1)`-Lipschitz map, so the Lipschitz image bound gives
`Hⁿ(G(piece)) ≤ (‖A‖ + 1)ⁿ η Lⁿ(piece)`.  Near a point with injective differential, the
differential is antilipschitz and the mean value inequality gives the injectivity and the lower
Lipschitz bound on a small ball; Lindelöf selects countably many such balls, which are enumerated
(padded with an injective linear map). -/
theorem aetp_rectifiable_c1_piece_cover : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (M : Set (Amb n ℓ)), Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ Z₀ : Set (Amb n ℓ), MeasurableSet Z₀ ∧ (μHE[n] : Measure (Amb n ℓ)) Z₀ = 0 ∧ ∃ (G : ℕ → Rn n → Amb n ℓ) (c : ℕ → Rn n) (r σ : ℕ → ℝ), (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, 0 < r k) ∧ (∀ k, 0 < σ k) ∧ (∀ k, ∀ b ∈ ball (c k) (r k), Function.Injective (fderiv ℝ (G k) b)) ∧ (∀ k, ∀ b₁ ∈ ball (c k) (r k), ∀ b₂ ∈ ball (c k) (r k), σ k * ‖b₁ - b₂‖ ≤ ‖G k b₁ - G k b₂‖) ∧ M ⊆ Z₀ ∪ ⋃ k, G k '' ball (c k) (r k) := by
  intro n ℓ hn M hM
  obtain ⟨M₀, hM₀, F, hF, hMcov⟩ := hM
  choose K hK using hF
  have hHvol : (μHE[n] : Measure (Rn n)) = volume := EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  -- The map squeezing the direction of a unit vector `u` by the factor `η` has determinant `η`.
  have hdet : ∀ (u : Rn n), ‖u‖ = 1 → ∀ (η : ℝ),
      LinearMap.det ((ContinuousLinearMap.id ℝ (Rn n) - (1 - η) • (innerSL ℝ u).smulRight u :
        Rn n →L[ℝ] Rn n) : Rn n →ₗ[ℝ] Rn n) = η := by
    intro u hu η
    set Θ : Rn n →L[ℝ] Rn n := ContinuousLinearMap.id ℝ (Rn n) - (1 - η) • (innerSL ℝ u).smulRight u
    have hΘ : ∀ x, Θ x = x - ((1 - η) * inner ℝ u x) • u := by
      intro x; simp [Θ, mul_smul]
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    set P : Submodule ℝ (Rn n) := ℝ ∙ u
    have hP : ∀ k ∈ P, Θ k = η • k := by
      intro k hk
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hk
      rw [hΘ]
      have : inner ℝ u (c • u) = c := by rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hu]; ring
      rw [this, smul_smul, ← sub_smul]; congr 1; ring
    have hP' : ∀ k ∈ Pᗮ, Θ k = k := by
      intro k hk
      rw [hΘ]
      have : inner ℝ u k = 0 :=
        Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self u) hk
      simp [this]
    let e := P.prodEquivOfIsCompl Pᗮ P.isCompl_orthogonal
    have hconj : e.symm.toLinearMap ∘ₗ (Θ : Rn n →ₗ[ℝ] Rn n) ∘ₗ e.symm.symm.toLinearMap =
        LinearMap.prodMap (η • LinearMap.id) LinearMap.id := by
      refine LinearMap.ext fun p => ?_
      obtain ⟨k, k'⟩ := p
      have hep : e.symm.symm (k, k') = (k : Rn n) + k' := rfl
      have hΘp : Θ ((k : Rn n) + k') = e (η • k, k') := by
        rw [map_add, hP k k.2, hP' k' k'.2]; rfl
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe, hep, hΘp,
        LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
    rw [← LinearMap.det_conj (Θ : Rn n →ₗ[ℝ] Rn n) e.symm, hconj, LinearMap.det_prodMap,
      LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id, finrank_span_singleton hu0]
    ring
  -- On a set where `H` is `η`-approximated by a non-injective linear map `A`, the `Hⁿ`-measure of
  -- the image is at most `(‖A‖ + 1)ⁿ η Lⁿ`.
  have key : ∀ (H : Rn n → Amb n ℓ) (A : Rn n →L[ℝ] Amb n ℓ) (s : Set (Rn n)) (L : ℝ) (η : ℝ≥0),
      ¬ Function.Injective A → ‖A‖ ≤ L → η ≤ 1 → ApproximatesLinearOn H A s η →
      (μHE[n] : Measure (Amb n ℓ)) (H '' s) ≤ ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by
    intro H A s L η hA hAL hη1 hHA
    obtain ⟨v, hv0, hAv⟩ : ∃ v, v ≠ 0 ∧ A v = 0 := by
      by_contra h
      push Not at h
      exact hA ((injective_iff_map_eq_zero A).2 fun v hv => by_contra fun hne => h v hne hv)
    set u : Rn n := ‖v‖⁻¹ • v with hu_def
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hv0
    have hAu : A u = 0 := by rw [hu_def, map_smul, hAv, smul_zero]
    have hL0 : 0 ≤ L := (norm_nonneg A).trans hAL
    have hη0 : (0 : ℝ) ≤ η := η.2
    have hη1' : (η : ℝ) ≤ 1 := hη1
    set Θ : Rn n →L[ℝ] Rn n := ContinuousLinearMap.id ℝ (Rn n) - (1 - (η : ℝ)) • (innerSL ℝ u).smulRight u
    have hΘ : ∀ x, Θ x = x - ((1 - (η : ℝ)) * inner ℝ u x) • u := by
      intro x; simp [Θ, mul_smul]
    have hΘn : ∀ x, ‖A x‖ + η * ‖x‖ ≤ (L + 1) * ‖Θ x‖ := by
      intro x
      set a := inner ℝ u x with ha
      have ha2 : a ^ 2 ≤ ‖x‖ ^ 2 := by
        have := abs_real_inner_le_norm u x
        rw [hu, one_mul] at this
        exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
      have hΘsq : ‖Θ x‖ ^ 2 = ‖x‖ ^ 2 - (1 - (η : ℝ) ^ 2) * a ^ 2 := by
        rw [hΘ, norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, mul_one, Real.norm_eq_abs,
          sq_abs, real_inner_comm u x, ← ha]
        ring
      set w := x - a • u with hw
      have hwsq : ‖w‖ ^ 2 = ‖x‖ ^ 2 - a ^ 2 := by
        rw [hw, norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, mul_one, Real.norm_eq_abs,
          sq_abs, real_inner_comm u x, ← ha]
        ring
      have hAx : A x = A w := by rw [hw, map_sub, map_smul, hAu, smul_zero, sub_zero]
      have h1 : ‖w‖ ≤ ‖Θ x‖ := by
        apply le_of_sq_le_sq _ (norm_nonneg _)
        rw [hwsq, hΘsq]; nlinarith [sq_nonneg (η : ℝ), sq_nonneg a]
      have h2 : (η : ℝ) * ‖x‖ ≤ ‖Θ x‖ := by
        apply le_of_sq_le_sq _ (norm_nonneg _)
        rw [hΘsq, mul_pow]
        have : 0 ≤ 1 - (η : ℝ) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left ha2 this]
      calc ‖A x‖ + η * ‖x‖ = ‖A w‖ + η * ‖x‖ := by rw [hAx]
        _ ≤ L * ‖w‖ + ‖Θ x‖ :=
          add_le_add ((A.le_opNorm w).trans (mul_le_mul_of_nonneg_right hAL (norm_nonneg w))) h2
        _ ≤ L * ‖Θ x‖ + ‖Θ x‖ := by gcongr
        _ = (L + 1) * ‖Θ x‖ := by ring
    have hHΘ : ∀ x ∈ s, ∀ y ∈ s, ‖H x - H y‖ ≤ (L + 1) * ‖Θ x - Θ y‖ := by
      intro x hx y hy
      have h := hHA x hx y hy
      calc ‖H x - H y‖ = ‖(H x - H y - A (x - y)) + A (x - y)‖ := by rw [sub_add_cancel]
        _ ≤ ‖H x - H y - A (x - y)‖ + ‖A (x - y)‖ := norm_add_le _ _
        _ ≤ η * ‖x - y‖ + ‖A (x - y)‖ := by gcongr
        _ = ‖A (x - y)‖ + η * ‖x - y‖ := add_comm _ _
        _ ≤ (L + 1) * ‖Θ (x - y)‖ := hΘn (x - y)
        _ = (L + 1) * ‖Θ x - Θ y‖ := by rw [map_sub]
    classical
    let Φ : Rn n → Amb n ℓ := fun y => H (Function.invFunOn Θ s y)
    have hΦ : ∀ x ∈ s, Φ (Θ x) = H x := by
      intro x hx
      have hex : ∃ a ∈ s, Θ a = Θ x := ⟨x, hx, rfl⟩
      have h1 := Function.invFunOn_mem hex
      have h2 := Function.invFunOn_eq hex
      have := hHΘ _ h1 x hx
      rw [h2, sub_self, norm_zero, mul_zero] at this
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    have hΦlip : LipschitzOnWith (Real.toNNReal (L + 1)) Φ (Θ '' s) := by
      refine LipschitzOnWith.of_dist_le_mul fun y₁ hy₁ y₂ hy₂ => ?_
      obtain ⟨x₁, hx₁, rfl⟩ := hy₁
      obtain ⟨x₂, hx₂, rfl⟩ := hy₂
      rw [hΦ x₁ hx₁, hΦ x₂ hx₂, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith)]
      exact hHΘ x₁ hx₁ x₂ hx₂
    have himg : H '' s = Φ '' (Θ '' s) := by
      rw [image_image]; exact image_congr fun x hx => (hΦ x hx).symm
    have hvolΘ : (μHE[n] : Measure (Rn n)) (Θ '' s) = (η : ℝ≥0∞) * volume s := by
      rw [hHvol]
      have := MeasureTheory.Measure.addHaar_image_linearMap volume (Θ : Rn n →ₗ[ℝ] Rn n) s
      rw [ContinuousLinearMap.coe_coe] at this
      rw [this, hdet u hu, abs_of_nonneg hη0, ENNReal.ofReal_coe_nnreal]
    calc (μHE[n] : Measure (Amb n ℓ)) (H '' s) = μHE[n] (Φ '' (Θ '' s)) := by rw [himg]
      _ ≤ (Real.toNNReal (L + 1) : ℝ≥0∞) ^ n * μHE[n] (Θ '' s) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hΦlip
      _ = ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by rw [hvolΘ]; rfl
  -- The image of the critical set of a `C¹` map `ℝⁿ → ℝ^{n+ℓ}` is `Hⁿ`-null.
  have sard : ∀ H : Rn n → Amb n ℓ, ContDiff ℝ 1 H →
      (μHE[n] : Measure (Amb n ℓ)) (H '' {b | ¬ Function.Injective (fderiv ℝ H b)}) = 0 := by
    intro H hH
    set C := {b | ¬ Function.Injective (fderiv ℝ H b)}
    have hdiff : Differentiable ℝ H := hH.differentiable one_ne_zero
    have hcont : Continuous (fderiv ℝ H) := hH.continuous_fderiv one_ne_zero
    have hCclosed : IsClosed C := by
      have : IsOpen {b | Function.Injective (fderiv ℝ H b)} :=
        ContinuousLinearMap.isOpen_injective.preimage hcont
      exact this.isClosed_compl
    have hcov : H '' C ⊆ ⋃ R : ℕ, H '' (C ∩ closedBall 0 R) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨R, hR⟩ := exists_nat_ge ‖x‖
      exact mem_iUnion.2 ⟨R, x, ⟨hx, mem_closedBall_zero_iff.2 hR⟩, rfl⟩
    refine measure_mono_null hcov (measure_iUnion_null fun R => ?_)
    set s := C ∩ closedBall (0 : Rn n) R
    obtain ⟨L, hL⟩ :=
      (isCompact_closedBall (0 : Rn n) R).exists_bound_of_continuousOn hcont.continuousOn
    have hsmeas : MeasurableSet s := (hCclosed.inter isClosed_closedBall).measurableSet
    have hbound : ∀ η : ℝ≥0, η ≤ 1 → 0 < η → (μHE[n] : Measure (Amb n ℓ)) (H '' s) ≤
        ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by
      intro η hη1 hη0
      rcases s.eq_empty_or_nonempty with hse | hsne
      · simp [hse]
      obtain ⟨t, A, hdisj, htm, hst, hap, hA⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt H s (fderiv ℝ H)
          (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt) (fun _ => η) (fun _ => hη0.ne')
      have hsU : s = ⋃ m, s ∩ t m := by rw [← inter_iUnion]; exact (inter_eq_left.2 hst).symm
      calc (μHE[n] : Measure (Amb n ℓ)) (H '' s) = μHE[n] (⋃ m, H '' (s ∩ t m)) := by
            rw [← image_iUnion, ← hsU]
        _ ≤ ∑' m, (μHE[n] : Measure (Amb n ℓ)) (H '' (s ∩ t m)) := measure_iUnion_le _
        _ ≤ ∑' m, ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume (s ∩ t m)) := by
            refine ENNReal.tsum_le_tsum fun m => ?_
            obtain ⟨y, hy, hAy⟩ := hA hsne m
            refine key H (A m) (s ∩ t m) L η ?_ ?_ hη1 (hap m)
            · rw [hAy]; exact hy.1
            · rw [hAy]; exact hL y hy.2
        _ = ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume (⋃ m, s ∩ t m)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, measure_iUnion]
            · intro i j hij
              exact (hdisj hij).mono inter_subset_right inter_subset_right
            · exact fun m => hsmeas.inter (htm m)
        _ = ENNReal.ofReal (L + 1) ^ n * ((η : ℝ≥0∞) * volume s) := by rw [← hsU]
    have hV : volume s ≠ ∞ :=
      ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
    have hc : ENNReal.ofReal (L + 1) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hlim := ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hV)) (Or.inr hc)
    rw [zero_mul, mul_zero] at hlim
    refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hm)
    have := hbound ((m : ℝ≥0)⁻¹) (inv_le_one_of_one_le₀ (by exact_mod_cast hm))
      (inv_pos.2 (Nat.cast_pos.2 hm))
    rwa [ENNReal.coe_inv hm0, ENNReal.coe_natCast] at this
  -- Near a point with injective differential: injectivity and a lower Lipschitz bound on a ball.
  have loc : ∀ (H : Rn n → Amb n ℓ), ContDiff ℝ 1 H → ∀ b, Function.Injective (fderiv ℝ H b) →
      ∃ ρ > 0, ∃ σ > 0, (∀ b' ∈ ball b ρ, Function.Injective (fderiv ℝ H b')) ∧
        ∀ b₁ ∈ ball b ρ, ∀ b₂ ∈ ball b ρ, σ * ‖b₁ - b₂‖ ≤ ‖H b₁ - H b₂‖ := by
    intro H hH b hinj
    set D := fderiv ℝ H b
    obtain ⟨Ka, hKpos, hKa⟩ := (LinearMap.injective_iff_antilipschitz (D : Rn n →ₗ[ℝ] Amb n ℓ)).1 hinj
    have hKpos' : (0 : ℝ) < Ka := hKpos
    have hlow : ∀ x, ‖x‖ ≤ Ka * ‖D x‖ := by
      intro x
      have := hKa.le_mul_dist x 0
      simpa [dist_eq_norm] using this
    set s₀ : ℝ := (Ka : ℝ)⁻¹ with hs₀
    have hs₀pos : 0 < s₀ := inv_pos.2 hKpos'
    have hlow' : ∀ x, s₀ * ‖x‖ ≤ ‖D x‖ := by
      intro x
      rw [hs₀, inv_mul_le_iff₀ hKpos']
      exact hlow x
    have hcont : Continuous (fderiv ℝ H) := hH.continuous_fderiv one_ne_zero
    have hdiff : Differentiable ℝ H := hH.differentiable one_ne_zero
    obtain ⟨ρ, hρ, hρD⟩ := Metric.continuous_iff.1 hcont b (s₀ / 2) (by positivity)
    have hnear : ∀ b' ∈ ball b ρ, ‖fderiv ℝ H b' - D‖ < s₀ / 2 := fun b' hb' => by
      rw [← dist_eq_norm]; exact hρD b' hb'
    refine ⟨ρ, hρ, s₀ / 2, by positivity, ?_, ?_⟩
    · intro b' hb' x y hxy
      by_contra hne
      have hz : x - y ≠ 0 := sub_ne_zero.2 hne
      have h0 : fderiv ℝ H b' (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have h1 : ‖fderiv ℝ H b' (x - y) - D (x - y)‖ ≤ ‖fderiv ℝ H b' - D‖ * ‖x - y‖ :=
        (fderiv ℝ H b' - D).le_opNorm (x - y)
      rw [h0, zero_sub, norm_neg] at h1
      have h2 := hlow' (x - y)
      have h3 := hnear b' hb'
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 hz
      nlinarith
    · intro b₁ hb₁ b₂ hb₂
      have hmv : ‖(H b₁ - D b₁) - (H b₂ - D b₂)‖ ≤ s₀ / 2 * ‖b₁ - b₂‖ := by
        have := (convex_ball b ρ).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
          (f := fun x => H x - D x) (C := s₀ / 2) (fun x _ => (hdiff x).sub D.differentiableAt)
          (fun x hx => ?_) hb₂ hb₁
        · simpa using this
        · rw [fderiv_fun_sub (hdiff x) D.differentiableAt, ContinuousLinearMap.fderiv]
          exact (hnear x hx).le
      have h2 := hlow' (b₁ - b₂)
      have h3 : ‖D (b₁ - b₂)‖ ≤ ‖H b₁ - H b₂‖ + ‖(H b₁ - D b₁) - (H b₂ - D b₂)‖ := by
        rw [map_sub]
        calc ‖D b₁ - D b₂‖ = ‖(H b₁ - H b₂) - ((H b₁ - D b₁) - (H b₂ - D b₂))‖ := by
              congr 1; abel
          _ ≤ ‖H b₁ - H b₂‖ + ‖(H b₁ - D b₁) - (H b₂ - D b₂)‖ := norm_sub_le _ _
      linarith
  -- A `C¹` map with injective differential at `0`, used to pad the enumeration.
  obtain ⟨G₀, hG₀, hG₀inj⟩ :
      ∃ G₀ : Rn n → Amb n ℓ, ContDiff ℝ 1 G₀ ∧ Function.Injective (fderiv ℝ G₀ 0) := by
    let p : Fin (n + ℓ) → Fin n := fun q => ⟨q % n, Nat.mod_lt _ hn⟩
    have hp : Function.Surjective p := fun i => ⟨Fin.castAdd ℓ i, Fin.ext (Nat.mod_eq_of_lt i.2)⟩
    let E₀ : Rn n →ₗ[ℝ] Amb n ℓ := (WithLp.linearEquiv 2 ℝ (Fin (n + ℓ) → ℝ)).symm.toLinearMap ∘ₗ
      LinearMap.funLeft ℝ ℝ p ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
    have hE₀ : Function.Injective E₀ :=
      (WithLp.linearEquiv 2 ℝ (Fin (n + ℓ) → ℝ)).symm.injective.comp
        ((LinearMap.funLeft_injective_of_surjective ℝ ℝ p hp).comp
          (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective)
    refine ⟨LinearMap.toContinuousLinearMap E₀, (LinearMap.toContinuousLinearMap E₀).contDiff, ?_⟩
    rw [ContinuousLinearMap.fderiv]
    exact hE₀
  -- `C¹` approximation of the coordinates of the Lipschitz maps `F j`.
  have happrox : ∀ (i j : ℕ) (q : Fin (n + ℓ)), ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧
      volume {x | (F j x).ofLp q ≠ g x} < ((i : ℝ≥0∞) + 1)⁻¹ := by
    intro i j q
    exact aetp_lipschitz_c1_approximation n hn (fun x => (F j x).ofLp q) _
      ((EuclideanSpace.proj q : Amb n ℓ →L[ℝ] ℝ).lipschitzWith.comp (hK j)) _
      (ENNReal.inv_pos.2 (by simp))
  choose g hg hgvol using happrox
  let G : ℕ → ℕ → Rn n → Amb n ℓ := fun i j x => WithLp.toLp 2 (fun q => g i j q x)
  have hGC1 : ∀ i j, ContDiff ℝ 1 (G i j) := fun i j => contDiff_euclidean.2 fun q => hg i j q
  -- The points where `F j` differs from every approximation form a Lebesgue-null set.
  let Z : ℕ → Set (Rn n) := fun j => ⋂ i, {x | F j x ≠ G i j x}
  have hZvol : ∀ j, volume (Z j) = 0 := by
    intro j
    have hle : ∀ i : ℕ, volume (Z j) ≤ ((n + ℓ : ℕ) : ℝ≥0∞) * ((i : ℝ≥0∞) + 1)⁻¹ := by
      intro i
      calc volume (Z j) ≤ volume (⋃ q, {x | (F j x).ofLp q ≠ g i j q x}) := by
            refine measure_mono fun x hx => ?_
            have hx' : F j x ≠ G i j x := mem_iInter.1 hx i
            by_contra hcon
            simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hcon
            exact hx' (PiLp.ext fun q => hcon q)
        _ ≤ ∑ q, volume {x | (F j x).ofLp q ≠ g i j q x} := measure_iUnion_fintype_le _ _
        _ ≤ ∑ _q : Fin (n + ℓ), ((i : ℝ≥0∞) + 1)⁻¹ :=
            Finset.sum_le_sum fun q _ => (hgvol i j q).le
        _ = ((n + ℓ : ℕ) : ℝ≥0∞) * ((i : ℝ≥0∞) + 1)⁻¹ := by simp
    have h0 : Tendsto (fun i : ℕ => ((n + ℓ : ℕ) : ℝ≥0∞) * ((i : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun i : ℕ => ((i : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
        have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
        simpa [Function.comp_def] using this
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.natCast_ne_top (n + ℓ)))
    exact le_antisymm (ge_of_tendsto' h0 hle) zero_le
  have hFZ : ∀ j, (μHE[n] : Measure (Amb n ℓ)) (F j '' Z j) = 0 := by
    intro j
    refine le_antisymm ((Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      n ((hK j).lipschitzOnWith)).trans ?_) zero_le
    rw [hHvol, hZvol j, mul_zero]
  -- Radii and lower Lipschitz constants around the points with injective differential.
  have hloc' : ∀ (i j : ℕ) (b : Rn n), ∃ ρ : ℝ, 0 < ρ ∧ ∃ σ : ℝ, 0 < σ ∧
      (Function.Injective (fderiv ℝ (G i j) b) →
        (∀ b' ∈ ball b ρ, Function.Injective (fderiv ℝ (G i j) b')) ∧
          ∀ b₁ ∈ ball b ρ, ∀ b₂ ∈ ball b ρ, σ * ‖b₁ - b₂‖ ≤ ‖G i j b₁ - G i j b₂‖) := by
    intro i j b
    by_cases hb : Function.Injective (fderiv ℝ (G i j) b)
    · obtain ⟨ρ, hρ, σ, hσ, h1, h2⟩ := loc _ (hGC1 i j) b hb
      exact ⟨ρ, hρ, σ, hσ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, one_pos, 1, one_pos, fun h => absurd h hb⟩
  choose ρ hρ σ hσ hρσ using hloc'
  obtain ⟨ρ₀, hρ₀, σ₀, hσ₀, hG₀ball, hG₀low⟩ := loc G₀ hG₀ 0 hG₀inj
  -- Lindelöf: countably many of these balls cover the non-critical set of each `G i j`.
  have hT : ∀ i j, ∃ T : Set (Rn n), T.Countable ∧
      ⋃ b ∈ T, (ball b (ρ i j b) ∩ {_x | Function.Injective (fderiv ℝ (G i j) b)}) =
        ⋃ b, (ball b (ρ i j b) ∩ {_x | Function.Injective (fderiv ℝ (G i j) b)}) :=
    fun i j => TopologicalSpace.isOpen_iUnion_countable _ fun b => isOpen_ball.inter isOpen_const
  choose T hTc hTU using hT
  -- Enumerate the countably many pieces.
  let S : Set (ℕ × ℕ × Rn n) := ⋃ i, ⋃ j, (fun b => (i, j, b)) '' T i j
  have hS : S.Countable := countable_iUnion fun i => countable_iUnion fun j => (hTc i j).image _
  obtain ⟨e, he⟩ := (hS.insert (0, 0, 0)).exists_eq_range (insert_nonempty _ _)
  classical
  let valid : ℕ → Prop := fun k => Function.Injective (fderiv ℝ (G (e k).1 (e k).2.1) (e k).2.2)
  let Gk : ℕ → Rn n → Amb n ℓ := fun k => if valid k then G (e k).1 (e k).2.1 else G₀
  let ck : ℕ → Rn n := fun k => if valid k then (e k).2.2 else 0
  let rk : ℕ → ℝ := fun k => if valid k then ρ (e k).1 (e k).2.1 (e k).2.2 else ρ₀
  let σk : ℕ → ℝ := fun k => if valid k then σ (e k).1 (e k).2.1 (e k).2.2 else σ₀
  -- The exceptional set and its Borel null hull.
  let Zbad : Set (Amb n ℓ) := M₀ ∪ (⋃ j, F j '' Z j) ∪
    ⋃ i, ⋃ j, G i j '' {b | ¬ Function.Injective (fderiv ℝ (G i j) b)}
  have hZbad : (μHE[n] : Measure (Amb n ℓ)) Zbad = 0 :=
    measure_union_null (measure_union_null hM₀ (measure_iUnion_null hFZ))
      (measure_iUnion_null fun i => measure_iUnion_null fun j => sard _ (hGC1 i j))
  refine ⟨toMeasurable μHE[n] Zbad, measurableSet_toMeasurable _ _,
    by rw [measure_toMeasurable]; exact hZbad, Gk, ck, rk, σk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases h : valid k
    · simp only [Gk, h, ↓reduceIte]; exact hGC1 _ _
    · simp only [Gk, h, ↓reduceIte]; exact hG₀
  · intro k
    by_cases h : valid k
    · simp only [rk, h, ↓reduceIte]; exact hρ _ _ _
    · simp only [rk, h, ↓reduceIte]; exact hρ₀
  · intro k
    by_cases h : valid k
    · simp only [σk, h, ↓reduceIte]; exact hσ _ _ _
    · simp only [σk, h, ↓reduceIte]; exact hσ₀
  · intro k
    by_cases h : valid k
    · simp only [Gk, ck, rk, h, ↓reduceIte]; exact ((hρσ _ _ _) h).1
    · simp only [Gk, ck, rk, h, ↓reduceIte]; exact hG₀ball
  · intro k
    by_cases h : valid k
    · simp only [Gk, ck, rk, σk, h, ↓reduceIte]; exact ((hρσ _ _ _) h).2
    · simp only [Gk, ck, rk, σk, h, ↓reduceIte]; exact hG₀low
  · intro x hx
    rcases hMcov hx with hx0 | hx1
    · exact Or.inl (subset_toMeasurable _ _ (Or.inl (Or.inl hx0)))
    · obtain ⟨j, z, rfl⟩ := mem_iUnion.1 hx1
      by_cases hz : z ∈ Z j
      · exact Or.inl (subset_toMeasurable _ _ (Or.inl (Or.inr (mem_iUnion.2 ⟨j, mem_image_of_mem _ hz⟩))))
      · simp only [Z, mem_iInter, mem_ofPred_eq, not_forall, not_not] at hz
        obtain ⟨i, hi⟩ := hz
        by_cases hzC : Function.Injective (fderiv ℝ (G i j) z)
        · have hzU : z ∈ ⋃ b, (ball b (ρ i j b) ∩ {_x | Function.Injective (fderiv ℝ (G i j) b)}) :=
            mem_iUnion.2 ⟨z, mem_ball_self (hρ i j z), hzC⟩
          rw [← hTU i j] at hzU
          simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_prop] at hzU
          obtain ⟨b, hbT, hzb, hbinj⟩ := hzU
          have hmem : (i, j, b) ∈ range e := by
            rw [← he]
            exact Or.inr (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, mem_image_of_mem _ hbT⟩⟩)
          obtain ⟨k, hk⟩ := hmem
          have hv : valid k := by simp only [valid, hk]; exact hbinj
          refine Or.inr (mem_iUnion.2 ⟨k, ?_⟩)
          simp only [Gk, ck, rk, hv, ↓reduceIte, hk]
          exact ⟨z, hzb, hi.symm⟩
        · exact Or.inl (subset_toMeasurable _ _
            (Or.inr (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, ⟨z, hzC, hi.symm⟩⟩⟩)))
/-- **Approximate tangent spaces of a bi-Lipschitz `C¹` chart image** (Simon Ch. 3, Def. 1.4):
if `G : ℝⁿ → ℝ^{n+ℓ}` is `C¹`, `DG(v)` is injective and `κ|v − w| ≤ |G v − G w|` on the open ball
`B̆_ρ(c)`, then `N = G(B̆_ρ(c))` is Borel with `Hⁿ(N) < ∞`, and `T(x) = DG(ψ x)(ℝⁿ)` (`ψ` the inverse
chart) is the approximate tangent space of `N` at every `x ∈ N`, with `x ↦ p_{T(x)}` continuous on
`N`.  Proof: `N` is `σ`-compact, and the Lipschitz image bound gives `Hⁿ(N) < ∞`; the projection
onto `L(ℝⁿ)` is `L (Lᵀ L)⁻¹ Lᵀ`, continuous in injective `L`.  For the tangent limit at `x = G w`,
the rescaled chart `Φ_r(s) = r⁻¹ (G(w + r s) − G w)`, reparametrized over an isometry
`ι : ℝⁿ → DG(w)(ℝⁿ)`, is `(1 ± ε)`-bi-Lipschitz on a fixed ball `D` for small `r` (mean value
inequality); so `Hⁿ` on its image is squeezed between `(1 ± ε)ⁿ` times the pushforward of Lebesgue
measure on `D` (the Lipschitz image bound replaces the area formula), and dominated convergence
gives `∫_{η_{x,r}(N)} f dHⁿ → ∫_D f ∘ ι = ∫_{T(x)} f dHⁿ`; the lower bound `κ` keeps the support of
`f ∘ Φ_r` inside `D`. -/
theorem tae_c1_chart_image_approxTangent : ∀ {n ℓ : ℕ} (G : Rn n → Amb n ℓ) (c : Rn n) (ρ κ : ℝ), 1 ≤ n → ContDiff ℝ 1 G → 0 < κ → (∀ v ∈ ball c ρ, Function.Injective (fderiv ℝ G v)) → (∀ v ∈ ball c ρ, ∀ w ∈ ball c ρ, κ * ‖v - w‖ ≤ ‖G v - G w‖) → MeasurableSet (G '' ball c ρ) ∧ (μHE[n] : Measure (Amb n ℓ)) (G '' ball c ρ) < ⊤ ∧ ∃ T : Amb n ℓ → Submodule ℝ (Amb n ℓ), ContinuousOn (fun x => (T x).starProjection) (G '' ball c ρ) ∧ ∀ x ∈ G '' ball c ρ, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (G '' ball c ρ) x (T x) := by
  intro n ℓ G c ρ κ hn hG hκ hinj hlow
  -- Step A (parent steps 0, 1, 3): `N = G(B')` is Borel and `Hⁿ(N) < ∞`.
  have hmeasfin : MeasurableSet (G '' ball c ρ) ∧ (μHE[n] : Measure (Amb n ℓ)) (G '' ball c ρ) < ⊤ := by
    have hGc : Continuous G := hG.continuous
    constructor
    · have hσ : IsSigmaCompact (ball c ρ) := by
        refine ⟨fun m : ℕ => closedBall c (ρ - 1 / ((m : ℝ) + 1)),
          fun m => isCompact_closedBall _ _, ?_⟩
        ext v
        simp only [mem_iUnion, mem_closedBall, mem_ball]
        constructor
        · rintro ⟨m, hm⟩
          have : 0 < 1 / ((m : ℝ) + 1) := by positivity
          linarith
        · intro hv
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hv)
          exact ⟨m, by linarith⟩
      obtain ⟨K, hK, hKU⟩ := hσ.image hGc
      rw [← hKU]
      exact MeasurableSet.iUnion fun j => (hK j).measurableSet
    · rcases le_or_gt ρ 0 with hρ | hρ
      · rw [ball_eq_empty.mpr hρ, image_empty, measure_empty]
        exact ENNReal.zero_lt_top
      · have hcont : Continuous (fun v => ‖fderiv ℝ G v‖₊) :=
          (hG.continuous_fderiv one_ne_zero).nnnorm
        obtain ⟨v₀, -, hv₀⟩ := (isCompact_closedBall c ρ).exists_isMaxOn
          (nonempty_closedBall.mpr hρ.le) hcont.continuousOn
        have hLip : LipschitzOnWith ‖fderiv ℝ G v₀‖₊ G (ball c ρ) :=
          (convex_ball c ρ).lipschitzOnWith_of_nnnorm_fderiv_le
            (fun v _ => (hG.differentiable one_ne_zero).differentiableAt)
            (fun v hv => hv₀ (ball_subset_closedBall hv))
        have himg := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip
        refine lt_of_le_of_lt himg (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ?_)
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
        exact measure_ball_lt_top
  -- Step B (parent step 5): `L ↦ p_{L(ℝⁿ)}` is continuous on injective `L`, via `L (Lᵀ L)⁻¹ Lᵀ`.
  have hproj : ContinuousOn (fun L : Rn n →L[ℝ] Amb n ℓ => (LinearMap.range L.toLinearMap).starProjection) {L : Rn n →L[ℝ] Amb n ℓ | Function.Injective L} := by
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
  -- Step C (parent steps 6-8): `DG(w)(ℝⁿ)` is the approximate tangent space of `N` at `G w`.
  have htan : ∀ w ∈ ball c ρ, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (G '' ball c ρ) (G w) (LinearMap.range (fderiv ℝ G w).toLinearMap) := by
    intro w hw
    have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
    have hDc : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
    set L := fderiv ℝ G w
    have hLinj : Function.Injective L := hinj w hw
    set P : Submodule ℝ (Amb n ℓ) := LinearMap.range L.toLinearMap with hPdef
    have hPdim : Module.finrank ℝ P = n := by
      rw [hPdef, LinearMap.finrank_range_of_inj hLinj, finrank_euclideanSpace_fin]
    refine ⟨hPdim, fun f => ?_⟩
    -- An isometric parametrization `ιL` of the plane `P`, and `A = ιL⁻¹ ∘ L` with inverse `Bc`.
    let e : P ≃ₗᵢ[ℝ] Rn n := ((stdOrthonormalBasis ℝ P).reindex (finCongr hPdim)).repr
    let ιL : Rn n →ₗᵢ[ℝ] Amb n ℓ := P.subtypeₗᵢ.comp e.symm.toLinearIsometry
    have hιrange : Set.range ιL = (P : Set (Amb n ℓ)) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact (e.symm z).2
      · intro hy
        exact ⟨e ⟨y, hy⟩, by simp [ιL]⟩
    let A : Rn n ≃ₗ[ℝ] Rn n := (LinearEquiv.ofInjective L.toLinearMap hLinj).trans e.toLinearEquiv
    have hιA : ∀ s, ιL (A s) = L s := by
      intro s
      simp [ιL, A]
    let Bc : Rn n →L[ℝ] Rn n := LinearMap.toContinuousLinearMap (A.symm : Rn n →ₗ[ℝ] Rn n)
    have hBc : ∀ z, Bc z = A.symm z := fun z => by simp [Bc]
    have hBA : ∀ s, Bc (A s) = s := fun s => by rw [hBc, LinearEquiv.symm_apply_apply]
    have hLB : ∀ z, L (Bc z) = ιL z := by
      intro z
      have h := hιA (A.symm z)
      simp only [LinearEquiv.apply_symm_apply] at h
      rw [hBc, h]
    have hAn : ∀ s, ‖A s‖ = ‖L s‖ := by
      intro s
      rw [← hιA, LinearIsometry.norm_map]
    set CB : ℝ := ‖Bc‖
    have hCB0 : 0 ≤ CB := norm_nonneg _
    have hB : ∀ z, ‖Bc z‖ ≤ CB * ‖z‖ := fun z => Bc.le_opNorm z
    -- The support radius `R` of `f` and the parameter ball `D`.
    obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
    set R : ℝ := max R₀ 0
    have hR0 : 0 ≤ R := le_max_right _ _
    have hfR : ∀ y : Amb n ℓ, R < ‖y‖ → f y = 0 := by
      intro y hy
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hR₀ hmem
      rw [mem_closedBall_zero_iff] at this
      linarith [le_max_left R₀ 0]
    set M : ℝ := R + ‖L‖ * R / κ
    have hRM : R ≤ M := by
      have : 0 ≤ ‖L‖ * R / κ := div_nonneg (mul_nonneg (norm_nonneg _) hR0) hκ.le
      linarith
    have hM0 : 0 ≤ M := hR0.trans hRM
    set D : Set (Rn n) := closedBall (0 : Rn n) M with hDdef
    have hCB1 : 0 < CB + 1 := add_pos_of_nonneg_of_pos hCB0 one_pos
    have hCBM : 0 < CB * M + 1 := add_pos_of_nonneg_of_pos (mul_nonneg hCB0 hM0) one_pos
    -- The rescaled chart `Φ r s = r⁻¹ (G (w + r s) - G w)` and its reparametrization `H r = Φ r ∘ Bc`.
    set Φ : ℝ → Rn n → Amb n ℓ := fun r s => r⁻¹ • (G (w + r • s) - G w) with hΦdef
    set Bp : ℝ → Set (Rn n) := fun r => (fun s => w + r • s) ⁻¹' ball c ρ with hBdef
    set H : ℝ → Rn n → Amb n ℓ := fun r z => Φ r (Bc z) with hHdef
    have haff : ∀ r : ℝ, Continuous (fun s : Rn n => w + r • s) := fun r =>
      continuous_const.add (continuous_id.const_smul r)
    have hΦc : ∀ r, Continuous (Φ r) := fun r =>
      ((hG.continuous.comp (haff r)).sub continuous_const).const_smul r⁻¹
    have hHc : ∀ r, Continuous (H r) := fun r => (hΦc r).comp Bc.continuous
    have hderiv : ∀ r : ℝ, r ≠ 0 → ∀ s, HasFDerivAt (Φ r) (fderiv ℝ G (w + r • s)) s := by
      intro r hr0 s
      have h1 : HasFDerivAt (fun s : Rn n => w + r • s) (r • ContinuousLinearMap.id ℝ (Rn n)) s :=
        ((hasFDerivAt_id s).const_smul r).const_add w
      have h2 := (((hGd (w + r • s)).hasFDerivAt.comp s h1).sub_const (G w)).const_smul r⁻¹
      have hfun : (r⁻¹ • fun x => (G ∘ fun s => w + r • s) x - G w) = Φ r := by
        funext x
        simp only [hΦdef, Pi.smul_apply, Function.comp_apply]
      have hlin : r⁻¹ • (fderiv ℝ G (w + r • s)).comp (r • ContinuousLinearMap.id ℝ (Rn n)) =
          fderiv ℝ G (w + r • s) := by
        refine ContinuousLinearMap.ext fun v => ?_
        rw [smul_apply, ContinuousLinearMap.comp_apply,
          smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_smul,
          inv_mul_cancel₀ hr0, one_smul]
      rw [hfun, hlin] at h2
      exact h2
    -- pointwise convergence `Φ r s → L s`
    have hΦt : ∀ s, Tendsto (fun r => Φ r s) (𝓝[>] 0) (𝓝 (L s)) := by
      intro s
      have hd : HasDerivAt (fun t : ℝ => G (w + t • s)) (L s) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
        have h2 := (hGd (w + (0 : ℝ) • s)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
        rw [zero_smul, add_zero] at h2
        exact h2
      have h3 := hd.tendsto_slope_zero_right
      simpa [hΦdef] using h3
    have hHt : ∀ z, Tendsto (fun r => H r z) (𝓝[>] 0) (𝓝 (ιL z)) := by
      intro z
      rw [← hLB z]
      exact hΦt (Bc z)
    -- the blown-up set is `Φ r '' Bp r`, and it is measurable
    have himg : ∀ r : ℝ, r ≠ 0 →
        Poincare.SimonGMT.Chapter03.blowUpMap (G w) r '' (G '' ball c ρ) = Φ r '' Bp r := by
      intro r hr0
      ext y
      simp only [mem_image, mem_preimage, hΦdef, hBdef, Poincare.SimonGMT.Chapter03.blowUpMap]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨r⁻¹ • (v - w), ?_, ?_⟩
        · rw [smul_smul, mul_inv_cancel₀ hr0, one_smul, add_sub_cancel]
          exact hv
        · rw [smul_smul, mul_inv_cancel₀ hr0, one_smul, add_sub_cancel]
      · rintro ⟨s, hs, rfl⟩
        exact ⟨G (w + r • s), ⟨w + r • s, hs, rfl⟩, rfl⟩
    have hmeasη : ∀ r : ℝ, r ≠ 0 →
        MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap (G w) r '' (G '' ball c ρ)) := by
      intro r hr0
      have hpre : Poincare.SimonGMT.Chapter03.blowUpMap (G w) r '' (G '' ball c ρ) =
          (fun y => G w + r • y) ⁻¹' (G '' ball c ρ) := by
        ext y
        constructor
        · rintro ⟨y₀, hy₀, rfl⟩
          show G w + r • (r⁻¹ • (y₀ - G w)) ∈ G '' ball c ρ
          rw [smul_smul, mul_inv_cancel₀ hr0, one_smul, add_sub_cancel]
          exact hy₀
        · intro hy
          refine ⟨G w + r • y, hy, ?_⟩
          show r⁻¹ • (G w + r • y - G w) = y
          rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr0, one_smul]
      rw [hpre]
      exact hmeasfin.1.preimage (continuous_const.add (continuous_id.const_smul r)).measurable
    -- `f` vanishes on `Φ r s` unless `s = Bc z` with `z ∈ D` (lower bound `κ`)
    have hfar : ∀ r : ℝ, 0 < r → ∀ s ∈ Bp r, (∀ z ∈ D, Bc z ≠ s) → f (Φ r s) = 0 := by
      intro r hr s hs hsD
      apply hfR
      have hAs : M < ‖A s‖ := by
        by_contra hcon
        exact hsD (A s) (mem_closedBall_zero_iff.mpr (not_lt.mp hcon)) (hBA s)
      have hsR : R / κ < ‖s‖ := by
        by_contra hcon
        have h1 : ‖L s‖ ≤ ‖L‖ * (R / κ) :=
          (L.le_opNorm s).trans (mul_le_mul_of_nonneg_left (not_lt.mp hcon) (norm_nonneg _))
        rw [hAn] at hAs
        have h2 : ‖L‖ * (R / κ) = ‖L‖ * R / κ := by ring
        linarith
      have h1 := hlow (w + r • s) hs w hw
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at h1
      have h2 : ‖Φ r s‖ = r⁻¹ * ‖G (w + r • s) - G w‖ := by
        simp only [hΦdef]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      rw [h2]
      have h3 : κ * ‖s‖ ≤ r⁻¹ * ‖G (w + r • s) - G w‖ := by
        rw [le_inv_mul_iff₀ hr]
        calc r * (κ * ‖s‖) = κ * (r * ‖s‖) := by ring
          _ ≤ _ := h1
      have h4 : R < κ * ‖s‖ := by
        rw [div_lt_iff₀ hκ] at hsR
        linarith
      linarith
    -- for small `r`, `Bc '' D ⊆ Bp r`, so the blow-up integral is an integral over `H r '' D`
    have hr₀ : 0 < (ρ - dist w c) / (CB * M + 1) :=
      div_pos (sub_pos.mpr (mem_ball.mp hw)) hCBM
    have hcover : ∀ r ∈ Ioo (0 : ℝ) ((ρ - dist w c) / (CB * M + 1)), ∀ z ∈ D, Bc z ∈ Bp r := by
      rintro r ⟨hr0, hr1⟩ z hz
      show w + r • Bc z ∈ ball c ρ
      rw [mem_ball]
      have h1 : ‖r • Bc z‖ ≤ r * (CB * M) := by
        rw [norm_smul, Real.norm_of_nonneg hr0.le]
        exact mul_le_mul_of_nonneg_left ((hB z).trans
          (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hCB0)) hr0.le
      have h2 : r * (CB * M) < ρ - dist w c := by
        rw [lt_div_iff₀ hCBM] at hr1
        linarith
      calc dist (w + r • Bc z) c ≤ dist (w + r • Bc z) w + dist w c := dist_triangle _ _ _
        _ = ‖r • Bc z‖ + dist w c := by rw [dist_eq_norm, add_sub_cancel_left]
        _ < ρ := by linarith
    have hsetint : ∀ r ∈ Ioo (0 : ℝ) ((ρ - dist w c) / (CB * M + 1)),
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (G w) r '' (G '' ball c ρ), f y
          ∂(μHE[n] : Measure (Amb n ℓ)) =
        ∫ y in H r '' D, f y ∂(μHE[n] : Measure (Amb n ℓ)) := by
      intro r hr
      have hr0 : r ≠ 0 := hr.1.ne'
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeasη r hr0)
      · rw [himg r hr0]
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨Bc z, hcover r hr z hz, rfl⟩
      · rintro y ⟨hy, hyH⟩
        rw [himg r hr0] at hy
        obtain ⟨s, hs, rfl⟩ := hy
        refine hfar r hr.1 s hs fun z hz hzs => hyH ⟨z, hz, ?_⟩
        simp only [hHdef, hzs]
    -- `H r` is `C¹`-close to the isometry `ιL` on `D` for small `r` (mean value inequality)
    have hLip : ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ D, ∀ z' ∈ D,
        ‖H r z - H r z' - (ιL z - ιL z')‖ ≤ ε * ‖z - z'‖ := by
      intro ε hε
      have hε' : 0 < ε / (CB + 1) := div_pos hε hCB1
      obtain ⟨η, hη, hηD⟩ := Metric.continuousAt_iff.mp hDc.continuousAt (ε / (CB + 1)) hε'
      have hr₁ : 0 < η / (CB * M + 1) := div_pos hη hCBM
      filter_upwards [Ioo_mem_nhdsGT hr₁] with r hr
      obtain ⟨hr0, hr1⟩ := hr
      intro z hz z' hz'
      have hsK : ∀ z ∈ D, Bc z ∈ closedBall (0 : Rn n) (CB * M) := fun z hz => by
        rw [mem_closedBall_zero_iff]
        exact (hB z).trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hCB0)
      set ψ : Rn n → Amb n ℓ := fun t => Φ r t - L t with hψdef
      have hψd : ∀ t ∈ closedBall (0 : Rn n) (CB * M),
          HasFDerivWithinAt ψ (fderiv ℝ G (w + r • t) - L) (closedBall (0 : Rn n) (CB * M)) t :=
        fun t _ => ((hderiv r hr0.ne' t).sub L.hasFDerivAt).hasFDerivWithinAt
      have hψb : ∀ t ∈ closedBall (0 : Rn n) (CB * M), ‖fderiv ℝ G (w + r • t) - L‖ ≤ ε / (CB + 1) := by
        intro t ht
        have h1 : dist (w + r • t) w < η := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le]
          have h2 : r * ‖t‖ ≤ r * (CB * M) :=
            mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp ht) hr0.le
          rw [lt_div_iff₀ hCBM] at hr1
          linarith
        have h3 := hηD h1
        rw [dist_eq_norm] at h3
        exact h3.le
      have hmvt := (convex_closedBall (0 : Rn n) (CB * M)).norm_image_sub_le_of_norm_hasFDerivWithin_le
        hψd hψb (hsK z' hz') (hsK z hz)
      have hkey : H r z - H r z' - (ιL z - ιL z') = ψ (Bc z) - ψ (Bc z') := by
        simp only [hψdef, hHdef]
        rw [hLB z, hLB z']
        abel
      rw [hkey]
      calc ‖ψ (Bc z) - ψ (Bc z')‖ ≤ ε / (CB + 1) * ‖Bc z - Bc z'‖ := hmvt
        _ = ε / (CB + 1) * ‖Bc (z - z')‖ := by rw [map_sub]
        _ ≤ ε / (CB + 1) * (CB * ‖z - z'‖) := mul_le_mul_of_nonneg_left (hB _) hε'.le
        _ ≤ ε * ‖z - z'‖ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hCB1]
          have h1 : 0 ≤ ε * ‖z - z'‖ := mul_nonneg hε.le (norm_nonneg _)
          linarith
    have hDfin : (volume : Measure (Rn n)) D < ∞ := measure_closedBall_lt_top
    -- Squeeze: for continuous `g ≥ 0`, `∫_{H r '' D} g dHⁿ → ∫_D g ∘ ιL` (bi-Lipschitz comparison
    -- of `Hⁿ ⌞ H r '' D` with the pushforward of Lebesgue measure on `D`)
    have hinner : ∀ g : Amb n ℓ → ℝ, Continuous g → (∀ y, 0 ≤ g y) → ∀ Cg : ℝ, (∀ y, g y ≤ Cg) →
        Tendsto (fun r => ∫ y in H r '' D, g y ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0)
          (𝓝 (∫ z in D, g (ιL z))) := by
      intro g hgc hg0 Cg hgC
      have hCg : 0 ≤ Cg := (hg0 0).trans (hgC 0)
      have hY : Tendsto (fun r => ∫ z in D, g (H r z)) (𝓝[>] 0) (𝓝 (∫ z in D, g (ιL z))) := by
        refine tendsto_integral_filter_of_dominated_convergence (fun _ => Cg) ?_ ?_ ?_ ?_
        · exact Eventually.of_forall fun r => (hgc.comp (hHc r)).aestronglyMeasurable
        · refine Eventually.of_forall fun r => Eventually.of_forall fun z => ?_
          rw [Real.norm_of_nonneg (hg0 _)]
          exact hgC _
        · exact integrableOn_const hDfin.ne
        · exact Eventually.of_forall fun z => (hgc.tendsto _).comp (hHt z)
      set K : ℝ := Cg * (volume : Measure (Rn n)).real D
      have hK0 : 0 ≤ K := mul_nonneg hCg measureReal_nonneg
      have hXY : Tendsto (fun r => ∫ y in H r '' D, g y ∂(μHE[n] : Measure (Amb n ℓ)) -
          ∫ z in D, g (H r z)) (𝓝[>] 0) (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro δ hδ
        -- choose `ε` with `((1 + ε)ⁿ - (1 - ε)ⁿ) K < δ`
        have hφc : Continuous fun ε : ℝ => ((1 + ε) ^ n - (1 - ε) ^ n) * K := by fun_prop
        have hφ0 : ((1 + (0 : ℝ)) ^ n - (1 - 0) ^ n) * K < δ := by simpa using hδ
        obtain ⟨ε, hεδ, hεI⟩ := ((((hφc.tendsto 0).eventually (gt_mem_nhds hφ0)).filter_mono
          nhdsWithin_le_nhds).and (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))).exists
        obtain ⟨hε0, hε1⟩ := hεI
        filter_upwards [hLip ε hε0, self_mem_nhdsWithin] with r hr hr0
        rw [mem_Ioi] at hr0
        -- bi-Lipschitz bounds for `H r` on `D`
        have hιsub : ∀ z z', ‖ιL z - ιL z'‖ = ‖z - z'‖ := fun z z' => by
          rw [← map_sub, LinearIsometry.norm_map]
        have hup : ∀ z ∈ D, ∀ z' ∈ D, ‖H r z - H r z'‖ ≤ (1 + ε) * ‖z - z'‖ := by
          intro z hz z' hz'
          have h1 := hr z hz z' hz'
          calc ‖H r z - H r z'‖ = ‖(H r z - H r z' - (ιL z - ιL z')) + (ιL z - ιL z')‖ := by
                rw [sub_add_cancel]
            _ ≤ ‖H r z - H r z' - (ιL z - ιL z')‖ + ‖ιL z - ιL z'‖ := norm_add_le _ _
            _ ≤ (1 + ε) * ‖z - z'‖ := by rw [hιsub]; linarith
        have hlo : ∀ z ∈ D, ∀ z' ∈ D, (1 - ε) * ‖z - z'‖ ≤ ‖H r z - H r z'‖ := by
          intro z hz z' hz'
          have h1 := hr z hz z' hz'
          have h2 : ‖ιL z - ιL z'‖ ≤ ‖H r z - H r z'‖ + ‖H r z - H r z' - (ιL z - ιL z')‖ := by
            calc ‖ιL z - ιL z'‖ = ‖(H r z - H r z') - (H r z - H r z' - (ιL z - ιL z'))‖ := by
                  rw [sub_sub_cancel]
              _ ≤ _ := norm_sub_le _ _
          rw [hιsub] at h2
          linarith
        have h1ε : 0 < 1 - ε := by linarith
        have hLipH : LipschitzOnWith (Real.toNNReal (1 + ε)) (H r) D := by
          refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
          rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith)]
          exact hup z hz z' hz'
        have hInjH : InjOn (H r) D := by
          intro z hz z' hz' hzz
          have h1 := hlo z hz z' hz'
          rw [hzz, sub_self, norm_zero] at h1
          have h2 : ‖z - z'‖ ≤ 0 := by
            by_contra hcon
            have h3 := mul_pos h1ε (lt_of_not_ge hcon)
            linarith
          exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
        set Hinv : Amb n ℓ → Rn n := Function.invFunOn (H r) D
        have hHinv : ∀ z ∈ D, Hinv (H r z) = z := fun z hz => hInjH.leftInvOn_invFunOn hz
        have hLipInv : LipschitzOnWith (Real.toNNReal (1 - ε)⁻¹) Hinv (H r '' D) := by
          refine LipschitzOnWith.of_dist_le_mul ?_
          rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
          rw [hHinv z hz, hHinv z' hz', dist_eq_norm, dist_eq_norm,
            Real.coe_toNNReal _ (inv_nonneg.mpr h1ε.le), inv_mul_eq_div, le_div_iff₀ h1ε]
          linarith [hlo z hz z' hz']
        -- comparison of `μ₁ = Hⁿ ⌞ H r '' D` with `ν = (H r)_# (Lⁿ ⌞ D)`
        have hHm : Measurable (H r) := (hHc r).measurable
        set μ₁ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)).restrict (H r '' D) with hμ₁def
        set ν : Measure (Amb n ℓ) := Measure.map (H r) ((volume : Measure (Rn n)).restrict D)
          with hνdef
        have hM1 : μ₁ ≤ ENNReal.ofReal ((1 + ε) ^ n) • ν := by
          rw [Measure.le_iff]
          intro S hS
          rw [Measure.smul_apply, hνdef, Measure.map_apply hHm hS,
            Measure.restrict_apply (hS.preimage hHm), hμ₁def, Measure.restrict_apply hS, smul_eq_mul]
          have h1 : S ∩ H r '' D = H r '' (D ∩ H r ⁻¹' S) := by
            rw [image_inter_preimage, inter_comm]
          have h2 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hLipH.mono (inter_subset_left : D ∩ H r ⁻¹' S ⊆ D))
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h2
          rw [h1, inter_comm (H r ⁻¹' S) D, ENNReal.ofReal_pow (by linarith)]
          exact h2
        have hM2 : ENNReal.ofReal ((1 - ε) ^ n) • ν ≤ μ₁ := by
          rw [Measure.le_iff]
          intro S hS
          rw [Measure.smul_apply, hνdef, Measure.map_apply hHm hS,
            Measure.restrict_apply (hS.preimage hHm), hμ₁def, Measure.restrict_apply hS, smul_eq_mul]
          have h1 : H r ⁻¹' S ∩ D ⊆ Hinv '' (S ∩ H r '' D) := by
            rintro z ⟨hzS, hzD⟩
            exact ⟨H r z, ⟨hzS, z, hzD, rfl⟩, hHinv z hzD⟩
          have h2 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hLipInv.mono (inter_subset_right : S ∩ H r '' D ⊆ H r '' D))
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h2
          have h3 : ENNReal.ofReal ((1 - ε) ^ n) * (ENNReal.ofReal (1 - ε)⁻¹) ^ n = 1 := by
            rw [← ENNReal.ofReal_pow (inv_nonneg.mpr h1ε.le),
              ← ENNReal.ofReal_mul (pow_nonneg h1ε.le n), ← mul_pow, mul_inv_cancel₀ h1ε.ne',
              one_pow, ENNReal.ofReal_one]
          calc ENNReal.ofReal ((1 - ε) ^ n) * volume (H r ⁻¹' S ∩ D)
              ≤ ENNReal.ofReal ((1 - ε) ^ n) * volume (Hinv '' (S ∩ H r '' D)) :=
                mul_le_mul_right (measure_mono h1) _
            _ ≤ ENNReal.ofReal ((1 - ε) ^ n) * ((ENNReal.ofReal (1 - ε)⁻¹) ^ n *
                (μHE[n] : Measure (Amb n ℓ)) (S ∩ H r '' D)) :=
                mul_le_mul_right h2 _
            _ = (μHE[n] : Measure (Amb n ℓ)) (S ∩ H r '' D) := by
                rw [← mul_assoc, h3, one_mul]
        -- integral comparison
        have : IsFiniteMeasure ν := by
          refine ⟨?_⟩
          rw [hνdef, Measure.map_apply hHm MeasurableSet.univ, preimage_univ,
            Measure.restrict_apply MeasurableSet.univ, univ_inter]
          exact hDfin
        have hμ₁fin : μ₁ univ < ∞ := by
          calc μ₁ univ ≤ (ENNReal.ofReal ((1 + ε) ^ n) • ν) univ := hM1 univ
            _ < ∞ := by
              rw [Measure.smul_apply, smul_eq_mul]
              exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν univ)
        have : IsFiniteMeasure μ₁ := ⟨hμ₁fin⟩
        have hgbd : ∀ y, ‖g y‖ ≤ Cg := fun y => by
          rw [Real.norm_of_nonneg (hg0 y)]
          exact hgC y
        have hgν : Integrable g ν :=
          Integrable.of_bound hgc.aestronglyMeasurable Cg (Eventually.of_forall hgbd)
        have hgμ₁ : Integrable g μ₁ :=
          Integrable.of_bound hgc.aestronglyMeasurable Cg (Eventually.of_forall hgbd)
        have hYeq : ∫ y, g y ∂ν = ∫ z in D, g (H r z) :=
          integral_map hHm.aemeasurable hgc.aestronglyMeasurable
        have hXle : ∫ y in H r '' D, g y ∂(μHE[n] : Measure (Amb n ℓ)) ≤
            (1 + ε) ^ n * ∫ z in D, g (H r z) := by
          have h := integral_mono_measure hM1 (Eventually.of_forall fun y => hg0 y)
            (hgν.smul_measure ENNReal.ofReal_ne_top)
          rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg (by linarith) n), smul_eq_mul,
            hYeq] at h
          exact h
        have hXge : (1 - ε) ^ n * ∫ z in D, g (H r z) ≤
            ∫ y in H r '' D, g y ∂(μHE[n] : Measure (Amb n ℓ)) := by
          have h := integral_mono_measure hM2 (Eventually.of_forall fun y => hg0 y) hgμ₁
          rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg h1ε.le n), smul_eq_mul,
            hYeq] at h
          exact h
        have hY0 : 0 ≤ ∫ z in D, g (H r z) :=
          setIntegral_nonneg measurableSet_closedBall fun z _ => hg0 _
        have hYK : ∫ z in D, g (H r z) ≤ K :=
          (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const hDfin fun z _ => hgbd _)
        have hpow1 : 1 ≤ (1 + ε) ^ n := one_le_pow₀ (by linarith)
        have hpow2 : (1 - ε) ^ n ≤ 1 := pow_le_one₀ h1ε.le (by linarith)
        rw [dist_zero_right, Real.norm_eq_abs, abs_lt]
        have ha := mul_le_mul_of_nonneg_left hYK (sub_nonneg.mpr hpow1)
        have hb := mul_le_mul_of_nonneg_left hYK (sub_nonneg.mpr hpow2)
        have ha0 := mul_nonneg (sub_nonneg.mpr hpow1) hK0
        have hb0 := mul_nonneg (sub_nonneg.mpr hpow2) hK0
        constructor
        · linarith
        · linarith
      have h := hXY.add hY
      simp only [sub_add_cancel, zero_add] at h
      exact h
    -- `f = f⁺ - f⁻` with `f^± ≥ 0` continuous; apply the squeeze to both parts
    obtain ⟨Cf, hCf⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    have hCf' : ∀ y, |f y| ≤ Cf := fun y => by
      rw [← Real.norm_eq_abs]
      exact hCf y
    have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf' 0)
    set fp : Amb n ℓ → ℝ := fun y => max (f y) 0
    set fm : Amb n ℓ → ℝ := fun y => max (-f y) 0
    have hfpc : Continuous fp := f.continuous.max continuous_const
    have hfmc : Continuous fm := f.continuous.neg.max continuous_const
    have hfpm : ∀ y, fp y - fm y = f y := fun y => max_zero_sub_max_neg_zero_eq_self (f y)
    have hfpC : ∀ y, fp y ≤ Cf := fun y => max_le ((le_abs_self _).trans (hCf' y)) hCf0
    have hfmC : ∀ y, fm y ≤ Cf := fun y => max_le ((neg_le_abs _).trans (hCf' y)) hCf0
    have hp := hinner fp hfpc (fun y => le_max_right _ _) Cf hfpC
    have hm := hinner fm hfmc (fun y => le_max_right _ _) Cf hfmC
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ∫ y in H r '' D, fp y ∂(μHE[n] : Measure (Amb n ℓ)) -
          ∫ y in H r '' D, fm y ∂(μHE[n] : Measure (Amb n ℓ)) =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (G w) r '' (G '' ball c ρ), f y
          ∂(μHE[n] : Measure (Amb n ℓ)) := by
      filter_upwards [hLip 1 one_pos, Ioo_mem_nhdsGT hr₀] with r hr hr'
      have hLipH : LipschitzOnWith (Real.toNNReal 2) (H r) D := by
        refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by norm_num)]
        have h1 := hr z hz z' hz'
        have h2 : ‖ιL z - ιL z'‖ = ‖z - z'‖ := by rw [← map_sub, LinearIsometry.norm_map]
        calc ‖H r z - H r z'‖ = ‖(H r z - H r z' - (ιL z - ιL z')) + (ιL z - ιL z')‖ := by
              rw [sub_add_cancel]
          _ ≤ ‖H r z - H r z' - (ιL z - ιL z')‖ + ‖ιL z - ιL z'‖ := norm_add_le _ _
          _ ≤ 2 * ‖z - z'‖ := by rw [h2]; linarith
      have hfin : (μHE[n] : Measure (Amb n ℓ)) (H r '' D) ≠ ∞ := by
        have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLipH
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
        exact (h.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hDfin)).ne
      have hip : IntegrableOn fp (H r '' D) (μHE[n] : Measure (Amb n ℓ)) :=
        Measure.integrableOn_of_bounded hfin hfpc.aestronglyMeasurable (M := Cf)
          (Eventually.of_forall fun y => by
            rw [Real.norm_of_nonneg (le_max_right _ _)]
            exact hfpC y)
      have him : IntegrableOn fm (H r '' D) (μHE[n] : Measure (Amb n ℓ)) :=
        Measure.integrableOn_of_bounded hfin hfmc.aestronglyMeasurable (M := Cf)
          (Eventually.of_forall fun y => by
            rw [Real.norm_of_nonneg (le_max_right _ _)]
            exact hfmC y)
      rw [hsetint r hr', ← integral_sub hip him]
      congr 1
      funext y
      exact hfpm y
    have hlim : (∫ z in D, fp (ιL z)) - ∫ z in D, fm (ιL z) =
        ∫ y in (P : Set (Amb n ℓ)), f y ∂(μHE[n] : Measure (Amb n ℓ)) := by
      have hιc : Continuous ιL := ιL.continuous
      have hi1 : IntegrableOn (fun z => fp (ιL z)) D (volume : Measure (Rn n)) :=
        (hfpc.comp hιc).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
      have hi2 : IntegrableOn (fun z => fm (ιL z)) D (volume : Measure (Rn n)) :=
        (hfmc.comp hιc).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
      rw [← integral_sub hi1 hi2]
      have h1 : ∫ z in D, (fp (ιL z) - fm (ιL z)) = ∫ z in D, f (ιL z) := by
        congr 1
        funext z
        exact hfpm _
      have hfc : Continuous (fun y : Amb n ℓ => f y) := f.continuous
      rw [h1, setIntegral_eq_integral_of_forall_compl_eq_zero, ← integral_map hιc.aemeasurable
        hfc.aestronglyMeasurable, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n,
        ιL.isometry.map_euclideanHausdorffMeasure, hιrange]
      intro z hz
      apply hfR
      rw [LinearIsometry.norm_map]
      rw [hDdef, mem_closedBall_zero_iff, not_le] at hz
      linarith
    rw [← hlim]
    exact (hp.sub hm).congr' hev
  -- Assembly (parent steps 2, 4): inverse chart `ψ`, `T x = DG(ψ x)(ℝⁿ)`.
  obtain ⟨hmeas, hfin⟩ := hmeasfin
  refine ⟨hmeas, hfin, ?_⟩
  -- the lower bound makes `G` injective on the ball
  have hInjOn : InjOn G (ball c ρ) := by
    intro v hv w hw hvw
    have h := hlow v hv w hw
    rw [hvw, sub_self, norm_zero] at h
    have h0 : ‖v - w‖ ≤ 0 := by
      by_contra hcon
      have := mul_pos hκ (lt_of_not_ge hcon)
      linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  -- the inverse chart `ψ` on `N = G(B')`, Lipschitz with constant `κ⁻¹`
  set ψ : Amb n ℓ → Rn n := Function.invFunOn G (ball c ρ) with hψdef
  have hψG : ∀ v ∈ ball c ρ, ψ (G v) = v := fun v hv => hInjOn.leftInvOn_invFunOn hv
  have hψmaps : MapsTo ψ (G '' ball c ρ) (ball c ρ) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hψG v hv]
    exact hv
  have hψcont : ContinuousOn ψ (G '' ball c ρ) := by
    have hL : LipschitzOnWith (Real.toNNReal κ⁻¹) ψ (G '' ball c ρ) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
      rw [hψG v hv, hψG w hw, dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.mpr hκ.le), inv_mul_eq_div, le_div_iff₀ hκ, mul_comm]
      exact hlow v hv w hw
    exact hL.continuousOn
  -- `T x = DG(ψ x)(ℝⁿ)`
  refine ⟨fun x => LinearMap.range (fderiv ℝ G (ψ x)).toLinearMap, ?_, ?_⟩
  · have hD : ContinuousOn (fun x => fderiv ℝ G (ψ x)) (G '' ball c ρ) :=
      (hG.continuous_fderiv one_ne_zero).comp_continuousOn hψcont
    have hmaps : MapsTo (fun x => fderiv ℝ G (ψ x)) (G '' ball c ρ)
        {L : Rn n →L[ℝ] Amb n ℓ | Function.Injective L} :=
      fun x hx => hinj _ (hψmaps hx)
    exact hproj.comp hD hmaps
  · rintro x ⟨w, hw, rfl⟩
    simp only [hψG w hw]
    exact htan w hw
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

/-- **Simon Ch. 3, Lemma 1.2 ("only if"), Remark 1.3 and Theorem 1.6 for `C¹` pieces.**  A
countably `n`-rectifiable `M ⊆ ℝ^{n+ℓ}` is covered, up to an `Hⁿ`-null set, by countably many Borel
sets `N_k` of finite `Hⁿ`-measure, each carrying approximate tangent planes `T_k(x)`, `x ∈ N_k`,
with `x ↦ p_{T_k(x)}` continuous on `N_k`.  Proof: the `C¹` piece cover (C¹ approximation of the
Lipschitz pieces, null critical images, Lindelöf) gives an `Hⁿ`-null `Z₀` and `C¹` charts `G_k`
with injective differential and a lower Lipschitz bound on balls `B_k`, with
`M ⊆ Z₀ ∪ ⋃_k G_k(B_k)`; take `N_k = G_k(B_k)` with the tangent field of each chart image, so
`M \ ⋃_k N_k ⊆ Z₀`. -/
theorem lipts_rectifiable_tangent_chart_cover : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (M : Set (Amb n ℓ)), Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ (N : ℕ → Set (Amb n ℓ)) (T : ℕ → Amb n ℓ → Submodule ℝ (Amb n ℓ)), (∀ k, MeasurableSet (N k)) ∧ (∀ k, (μHE[n] : Measure (Amb n ℓ)) (N k) < ⊤) ∧ (∀ k, ContinuousOn (fun x => (T k x).starProjection) (N k)) ∧ (∀ k, ∀ x ∈ N k, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (N k) x (T k x)) ∧ (μHE[n] : Measure (Amb n ℓ)) (M \ ⋃ k, N k) = 0 := by
  intro n ℓ hn M hM
  obtain ⟨Z₀, -, hZ₀, G, c, r, σ, hG, -, hσ, hinj, hlow, hcov⟩ :=
    aetp_rectifiable_c1_piece_cover n ℓ hn M hM
  have hchart := fun k => tae_c1_chart_image_approxTangent (G k) (c k) (r k) (σ k) hn (hG k)
    (hσ k) (hinj k) (hlow k)
  choose T hT using fun k => (hchart k).2.2
  refine ⟨fun k => G k '' ball (c k) (r k), T, fun k => (hchart k).1, fun k => (hchart k).2.1,
    fun k => (hT k).1, fun k => (hT k).2, measure_mono_null (fun x hx => ?_) hZ₀⟩
  rcases hcov hx.1 with h | h
  · exact h
  · exact absurd h hx.2
/-! ### `lip_approx_tangent_structure`: tangent planes, measurability and density of `V`

Parts D–H of the accepted natural proof (Simon Ch. 3, 1.6 "⇒", Remarks 1.8(1),(2), Theorem 1.9),
on top of the chart cover `lipts_rectifiable_tangent_chart_cover` (Parts A–C).  At `Hⁿ`-a.e. point
`y` of `M ∩ N_k`, the weighted blow-ups of `(M, θ)` are compared with `θ(y)` times the blow-ups of
`N_k`; the error is controlled by the Lebesgue differentiation theorem for `θ 1_{M ∩ K}` with
respect to `Hⁿ ⌞ N_k` (Besicovitch) and by the Upper Density Theorem
(`upperDensity_ne_zero_outside_hausdorff_null`) for `|θ| Hⁿ ⌞ (M ∩ K)` on `N_kᶜ`. -/

/-- `ω_n > 0`. -/
theorem liptsp_unitBallVolume_pos (n : ℕ) : 0 < unitBallVolume n :=
  div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))

/-- `|η_{y,r}(z)| = |z - y| / r` for `r > 0`. -/
theorem liptsp_norm_blowUp {n ℓ : ℕ} (y z : Amb n ℓ) {r : ℝ} (hr : 0 < r) :
    ‖Poincare.SimonGMT.Chapter03.blowUpMap y r z‖ = ‖z - y‖ / r := by
  rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le),
    inv_mul_eq_div]

/-- Scaling (S): `Hⁿ(η_{y,r}(S)) = r⁻ⁿ Hⁿ(S)` for every set `S` (a translation followed by a
homothety of ratio `r⁻¹`). -/
theorem liptsp_hausdorff_blowUp_image (n ℓ : ℕ) (y : Amb n ℓ) {r : ℝ} (hr : 0 < r)
    (S : Set (Amb n ℓ)) :
    (μHE[n] : Measure (Amb n ℓ)) (Poincare.SimonGMT.Chapter03.blowUpMap y r '' S) =
      ENNReal.ofReal r⁻¹ ^ n * (μHE[n] : Measure (Amb n ℓ)) S := by
  have hshift : Isometry (fun z : Amb n ℓ => z - y) :=
    Isometry.of_dist_eq fun a b => by simp only [dist_eq_norm, sub_sub_sub_cancel_right]
  have himage : Poincare.SimonGMT.Chapter03.blowUpMap y r '' S =
      AffineMap.homothety (0 : Amb n ℓ) r⁻¹ '' ((fun z => z - y) '' S) := by
    rw [← image_comp]
    congr 1
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Amb n ℓ) (inv_ne_zero hr.ne'),
    hshift.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow,
    ← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (inv_pos.mpr hr).le]

/-- Blow-up change of variables (S): for `r > 0` and any `S, f, w`,
`∫_{η(S)} f(z) w(y + r z) dHⁿ(z) = r⁻ⁿ ∫_S f(η z) w(z) dHⁿ(z)`; no integrability is needed. -/
theorem liptsp_blowUp_setIntegral_eq (n ℓ : ℕ) (S : Set (Amb n ℓ)) (f w : Amb n ℓ → ℝ)
    (y : Amb n ℓ) {r : ℝ} (hr : 0 < r) :
    ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' S, f z * w (y + r • z)
        ∂(μHE[n] : Measure (Amb n ℓ)) =
      (r ^ n)⁻¹ * ∫ z in S, f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) * w z
        ∂(μHE[n] : Measure (Amb n ℓ)) := by
  set η := Poincare.SimonGMT.Chapter03.blowUpMap y r with hη
  let e : Amb n ℓ ≃ₜ Amb n ℓ :=
    (Homeomorph.subRight y).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : ⇑e = η := rfl
  have hemb : MeasurableEmbedding η := he ▸ e.toMeasurableEquiv.measurableEmbedding
  have hinj : Function.Injective η := he ▸ e.injective
  have hsurj : Function.Surjective η := he ▸ e.surjective
  have hscale : ∀ T : Set (Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) (η '' T) =
      ENNReal.ofReal r⁻¹ ^ n * (μHE[n] : Measure (Amb n ℓ)) T :=
    fun T => liptsp_hausdorff_blowUp_image n ℓ y hr T
  have hmeas : (μHE[n] : Measure (Amb n ℓ)).restrict (η '' S) =
      (ENNReal.ofReal r⁻¹ ^ n) • ((μHE[n] : Measure (Amb n ℓ)).restrict S).map η := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply hemb.measurable hA,
      Measure.restrict_apply (hemb.measurable hA), smul_eq_mul, ← hscale, image_inter hinj,
      image_preimage_eq A hsurj]
  rw [hmeas, integral_smul_measure, hemb.integral_map, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (inv_pos.mpr hr).le, inv_pow, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hη, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne',
    one_smul, add_sub_cancel]

/-- `η_{y,r}(B_{rA}(y) ∩ S) = B_A(0) ∩ η_{y,r}(S)` for `r > 0`. -/
theorem liptsp_blowUp_image_inter_closedBall {n ℓ : ℕ} (y : Amb n ℓ) {r A : ℝ} (hr : 0 < r)
    (S : Set (Amb n ℓ)) :
    Poincare.SimonGMT.Chapter03.blowUpMap y r '' (closedBall y (r * A) ∩ S) =
      closedBall (0 : Amb n ℓ) A ∩ Poincare.SimonGMT.Chapter03.blowUpMap y r '' S := by
  have hmem : ∀ x : Amb n ℓ, Poincare.SimonGMT.Chapter03.blowUpMap y r x ∈
      closedBall (0 : Amb n ℓ) A ↔ x ∈ closedBall y (r * A) := by
    intro x
    rw [mem_closedBall_zero_iff, liptsp_norm_blowUp y x hr, div_le_iff₀ hr, mem_closedBall,
      dist_eq_norm, mul_comm A r]
  ext z
  constructor
  · rintro ⟨x, ⟨hxB, hxS⟩, rfl⟩
    exact ⟨(hmem x).mpr hxB, mem_image_of_mem _ hxS⟩
  · rintro ⟨hzB, x, hxS, rfl⟩
    exact ⟨x, ⟨(hmem x).mp hzB, hxS⟩, rfl⟩

/-- Weighted blow-up change of variables: if `f ∘ η_{y,r}` vanishes off `K`, then
`∫_{η(M)} f(z) θ(y + r z) dHⁿ(z) = r⁻ⁿ ∫ f(η z) θ 1_{M ∩ K}(z) dHⁿ(z)`. -/
theorem liptsp_blowUp_weighted_eq {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
    (K : Set (Amb n ℓ)) (f : Amb n ℓ → ℝ) (y : Amb n ℓ) {r : ℝ} (hr : 0 < r)
    (hf0 : ∀ z, z ∉ K → f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) = 0) :
    ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' V.carrier, f z * V.mult (y + r • z)
        ∂(μHE[n] : Measure (Amb n ℓ)) =
      (r ^ n)⁻¹ * ∫ z, f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
        (V.carrier ∩ K).indicator V.mult z ∂(μHE[n] : Measure (Amb n ℓ)) := by
  rw [liptsp_blowUp_setIntegral_eq n ℓ V.carrier f V.mult y hr,
    ← integral_indicator₀ V.nullMeasurableSet_carrier]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  by_cases hzM : z ∈ V.carrier
  · rw [indicator_of_mem hzM]
    by_cases hzK : z ∈ K
    · rw [indicator_of_mem (Set.mem_inter hzM hzK)]
    · rw [hf0 z hzK, zero_mul, zero_mul]
  · rw [indicator_of_notMem hzM,
      indicator_of_notMem (fun h : z ∈ V.carrier ∩ K => hzM h.1), mul_zero]

/-- Radial cut-offs: for `ε > 0` there is `φ ∈ C_c` with values in `[0, 1]`, `φ = 1` on `B_1(0)`
and `φ = 0` off `B_{1+ε}(0)`. -/
theorem liptsp_exists_cutoff {n ℓ : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : CompactlySupportedContinuousMap (Amb n ℓ) ℝ, (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧
      (∀ z, ‖z‖ ≤ 1 → φ z = 1) ∧ (∀ z, 1 + ε < ‖z‖ → φ z = 0) := by
  have hzero : ∀ z : Amb n ℓ, 1 + ε < ‖z‖ → min 1 (max 0 ((1 + ε - ‖z‖) / ε)) = 0 := by
    intro z hz
    have h : (1 + ε - ‖z‖) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    rw [max_eq_left h, min_eq_right zero_le_one]
  refine ⟨⟨⟨fun z => min 1 (max 0 ((1 + ε - ‖z‖) / ε)),
    continuous_const.min (continuous_const.max ((continuous_const.sub continuous_norm).div_const ε))⟩,
    HasCompactSupport.intro (isCompact_closedBall (0 : Amb n ℓ) (1 + ε)) fun z hz => ?_⟩,
    fun z => ⟨?_, ?_⟩, fun z hz => ?_, fun z hz => hzero z hz⟩
  · rw [mem_closedBall_zero_iff, not_le] at hz
    exact hzero z hz
  · exact le_min zero_le_one (le_max_left _ _)
  · exact min_le_left _ _
  · have h : 1 ≤ (1 + ε - ‖z‖) / ε := by
      rw [le_div_iff₀ hε]
      linarith
    change min 1 (max 0 ((1 + ε - ‖z‖) / ε)) = 1
    rw [max_eq_right (zero_le_one.trans h), min_eq_left h]

/-- `Hⁿ(P ∩ B_s(0)) = ω_n sⁿ` for an `n`-dimensional subspace `P` and `s ≥ 0` (the inclusion of
`P` is an isometry and `Hⁿ` is Lebesgue measure on `P`). -/
theorem liptsp_planeMeasure_closedBall {n ℓ : ℕ} (hn : 1 ≤ n) {P : Submodule ℝ (Amb n ℓ)}
    (hP : Module.finrank ℝ P = n) {s : ℝ} (hs : 0 ≤ s) :
    ((μHE[n] : Measure (Amb n ℓ)).restrict (P : Set (Amb n ℓ))) (closedBall 0 s) =
      ENNReal.ofReal (unitBallVolume n * s ^ n) := by
  have : Nontrivial P := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hrange : range (P.subtypeₗᵢ : P → Amb n ℓ) = (P : Set (Amb n ℓ)) := by ext x; simp
  rw [← hrange, ← P.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure,
    Measure.map_apply P.subtypeₗᵢ.continuous.measurable measurableSet_closedBall]
  have hpre : (P.subtypeₗᵢ : P → Amb n ℓ) ⁻¹' closedBall (0 : Amb n ℓ) s =
      closedBall (0 : P) s := by
    ext x; simp [mem_closedBall, dist_eq_norm]
  have hvol : (μHE[n] : Measure P) = volume := by
    have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := P); rwa [hP] at h
  have hsq : √Real.pi ^ n = Real.pi ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    ring
  rw [hpre, hvol, InnerProductSpace.volume_closedBall, hP, ← ENNReal.ofReal_pow hs,
    ← ENNReal.ofReal_mul (pow_nonneg hs n), hsq]
  congr 1
  unfold unitBallVolume
  ring

/-- Upper mass bound (δ) from an approximate tangent plane: `r⁻ⁿ Hⁿ(N ∩ B_r(y))` stays bounded
as `r → 0+` (test the definition with a cut-off `≥ 1_{B_1(0)}`). -/
theorem liptsp_ballMass_bound {n ℓ : ℕ} {N : Set (Amb n ℓ)}
    (hNfin : (μHE[n] : Measure (Amb n ℓ)) N < ⊤) {y : Amb n ℓ} {P : Submodule ℝ (Amb n ℓ)}
    (hP : Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N y P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal ((s ^ n)⁻¹) * (μHE[n] : Measure (Amb n ℓ)).restrict N (closedBall y s) ≤
        C := by
  obtain ⟨φ, hφ01, hφ1, -⟩ := liptsp_exists_cutoff (n := n) (ℓ := ℓ) one_pos
  refine ⟨ENNReal.ofReal ((∫ z in (P : Set (Amb n ℓ)), φ z ∂(μHE[n] : Measure (Amb n ℓ))) + 1),
    ENNReal.ofReal_ne_top, ?_⟩
  filter_upwards [self_mem_nhdsWithin, (hP.2 φ).eventually (gt_mem_nhds (lt_add_one _))]
    with s hs hsφ
  have hs0 : 0 < s := hs
  have hηN : (μHE[n] : Measure (Amb n ℓ)) (Poincare.SimonGMT.Chapter03.blowUpMap y s '' N) < ⊤ := by
    rw [liptsp_hausdorff_blowUp_image n ℓ y hs0]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hNfin
  have hφi : IntegrableOn φ (Poincare.SimonGMT.Chapter03.blowUpMap y s '' N)
      (μHE[n] : Measure (Amb n ℓ)) :=
    Measure.integrableOn_of_bounded hηN.ne φ.continuous.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_of_nonneg (hφ01 z).1]; exact (hφ01 z).2)
  calc ENNReal.ofReal ((s ^ n)⁻¹) * (μHE[n] : Measure (Amb n ℓ)).restrict N (closedBall y s)
      = (μHE[n] : Measure (Amb n ℓ))
          (closedBall (0 : Amb n ℓ) 1 ∩ Poincare.SimonGMT.Chapter03.blowUpMap y s '' N) := by
        rw [Measure.restrict_apply measurableSet_closedBall,
          ← liptsp_blowUp_image_inter_closedBall y hs0 N, mul_one,
          liptsp_hausdorff_blowUp_image n ℓ y hs0, ← ENNReal.ofReal_pow (inv_nonneg.2 hs0.le),
          inv_pow]
    _ = ∫⁻ z, (closedBall (0 : Amb n ℓ) 1).indicator 1 z
          ∂(μHE[n] : Measure (Amb n ℓ)).restrict
            (Poincare.SimonGMT.Chapter03.blowUpMap y s '' N) := by
        rw [lintegral_indicator_one measurableSet_closedBall,
          Measure.restrict_apply measurableSet_closedBall]
    _ ≤ ∫⁻ z, ENNReal.ofReal (φ z) ∂(μHE[n] : Measure (Amb n ℓ)).restrict
            (Poincare.SimonGMT.Chapter03.blowUpMap y s '' N) := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ closedBall (0 : Amb n ℓ) 1
        · rw [indicator_of_mem hz, Pi.one_apply, hφ1 z (mem_closedBall_zero_iff.1 hz),
            ENNReal.ofReal_one]
        · rw [indicator_of_notMem hz]
          exact zero_le
    _ = ENNReal.ofReal (∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y s '' N, φ z
          ∂(μHE[n] : Measure (Amb n ℓ))) :=
        (ofReal_integral_eq_lintegral_ofReal hφi (Eventually.of_forall fun z => (hφ01 z).1)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsφ.le

/-- Lebesgue points and (δ) give `r⁻ⁿ ∫_{B_r(y)} h d(Hⁿ ⌞ N) → 0` once the averages
`∫_{B_r(y)} h d(Hⁿ ⌞ N) / Hⁿ(N ∩ B_r(y))` tend to `0`. -/
theorem liptsp_tendsto_scaled_lintegral {n ℓ : ℕ} {N : Set (Amb n ℓ)}
    (hNfin : (μHE[n] : Measure (Amb n ℓ)) N < ⊤) {y : Amb n ℓ} {P : Submodule ℝ (Amb n ℓ)}
    (hP : Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N y P)
    (h : Amb n ℓ → ℝ≥0∞)
    (hγ : Tendsto (fun s : ℝ => (∫⁻ z in closedBall y s, h z
        ∂(μHE[n] : Measure (Amb n ℓ)).restrict N) /
        (μHE[n] : Measure (Amb n ℓ)).restrict N (closedBall y s)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun s : ℝ => ENNReal.ofReal ((s ^ n)⁻¹) *
        ∫⁻ z in closedBall y s, h z ∂(μHE[n] : Measure (Amb n ℓ)).restrict N)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hbd⟩ := liptsp_ballMass_bound hNfin hP
  have hlim : Tendsto (fun s : ℝ => (∫⁻ z in closedBall y s, h z
      ∂(μHE[n] : Measure (Amb n ℓ)).restrict N) /
      (μHE[n] : Measure (Amb n ℓ)).restrict N (closedBall y s) * C) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hγ (Or.inr hC)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun s => zero_le) ?_
  filter_upwards [hbd] with s hs
  have hb : (μHE[n] : Measure (Amb n ℓ)).restrict N (closedBall y s) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hNfin.ne ?_
    rw [Measure.restrict_apply measurableSet_closedBall]
    exact measure_mono inter_subset_right
  have hL : (∫⁻ z in closedBall y s, h z ∂(μHE[n] : Measure (Amb n ℓ)).restrict N) =
      (∫⁻ z in closedBall y s, h z ∂(μHE[n] : Measure (Amb n ℓ)).restrict N) /
        (μHE[n] : Measure (Amb n ℓ)).restrict N (closedBall y s) *
        (μHE[n] : Measure (Amb n ℓ)).restrict N (closedBall y s) :=
    (ENNReal.div_mul_cancel' (fun hb0 => setLIntegral_measure_zero _ _ hb0)
      (fun hbt => absurd hbt hb)).symm
  calc ENNReal.ofReal ((s ^ n)⁻¹) *
        ∫⁻ z in closedBall y s, h z ∂(μHE[n] : Measure (Amb n ℓ)).restrict N
      = (∫⁻ z in closedBall y s, h z ∂(μHE[n] : Measure (Amb n ℓ)).restrict N) /
          (μHE[n] : Measure (Amb n ℓ)).restrict N (closedBall y s) *
        (ENNReal.ofReal ((s ^ n)⁻¹) *
          (μHE[n] : Measure (Amb n ℓ)).restrict N (closedBall y s)) := by
        conv_lhs => rw [hL]
        exact mul_left_comm _ _ _
    _ ≤ _ := by gcongr

/-- **Weighted tangent plane at a good point** (Parts D–E for one chart).  Let `N` be Borel with
`Hⁿ(N) < ∞` and approximate tangent plane `P` at `y ∈ M`, let `K ⊆ U` be compact with
`B_{δ₀}(y) ⊆ K`, and put `g = θ 1_{M ∩ K}`.  If `y` is a Lebesgue point of `g` for `Hⁿ ⌞ N` (hγ)
and `|g| Hⁿ` has zero `n`-density on `Nᶜ` at `y` (hα), then `P` is the weighted approximate tangent
plane of `(M, θ)` at `y`: for `f ∈ C_c` vanishing off `B_R(0)` and small `r`,
`∫_{η(M)} f θ(y + r·) − θ(y) ∫_{η(N)} f = r⁻ⁿ (∫_N (f∘η)(g − g(y)) + ∫_{Nᶜ} (f∘η) g)`. -/
theorem liptsp_weighted_of_lebesgue_point {n ℓ : ℕ} {U : Set (Amb n ℓ)}
    (V : RectifiableVarifold n ℓ U) {N K : Set (Amb n ℓ)} (hNm : MeasurableSet N)
    (hNfin : (μHE[n] : Measure (Amb n ℓ)) N < ⊤) (hKc : IsCompact K) (hKU : K ⊆ U)
    {y : Amb n ℓ} {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hyK : closedBall y δ₀ ⊆ K) (hyM : y ∈ V.carrier)
    {P : Submodule ℝ (Amb n ℓ)}
    (hP : Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N y P)
    (hα : Tendsto (fun s : ℝ => ((μHE[n] : Measure (Amb n ℓ)).withDensity
        fun z => ‖(V.carrier ∩ K).indicator V.mult z‖ₑ) (Nᶜ ∩ closedBall y s) /
        ENNReal.ofReal (unitBallVolume n * s ^ n)) (𝓝[>] 0) (𝓝 0))
    (hγ : Tendsto (fun s : ℝ => (∫⁻ z in closedBall y s, ‖(V.carrier ∩ K).indicator V.mult z -
        (V.carrier ∩ K).indicator V.mult y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)).restrict N) /
        (μHE[n] : Measure (Amb n ℓ)).restrict N (closedBall y s)) (𝓝[>] 0) (𝓝 0)) :
    Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult y P := by
  have hMK : NullMeasurableSet (V.carrier ∩ K) (μHE[n] : Measure (Amb n ℓ)) :=
    V.nullMeasurableSet_carrier.inter hKc.isClosed.measurableSet.nullMeasurableSet
  have hgi : Integrable ((V.carrier ∩ K).indicator V.mult) (μHE[n] : Measure (Amb n ℓ)) :=
    (V.integrableOn_mult K hKc hKU).integrable_indicator₀ hMK
  have hgy : (V.carrier ∩ K).indicator V.mult y = V.mult y :=
    indicator_of_mem (Set.mem_inter hyM (hyK (mem_closedBall_self hδ₀.le))) _
  have hγ' := liptsp_tendsto_scaled_lintegral hNfin hP _ hγ
  refine ⟨hP.1, fun f => ?_⟩
  -- A support radius `R` and a bound `Cf` for the test function `f`.
  obtain ⟨R0, hR0⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
  obtain ⟨R, hR, hfR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ z, f z ≠ 0 → ‖z‖ ≤ R := by
    refine ⟨max R0 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz => ?_⟩
    have hz' := hR0 (subset_tsupport _ hz)
    rw [mem_closedBall, dist_zero_right] at hz'
    exact hz'.trans (le_max_left _ _)
  obtain ⟨Cf, hCf⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  have hfb : ∀ z, ‖f z‖ₑ ≤ ENNReal.ofReal Cf := fun z => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hCf z)
  have hsupp : ∀ r : ℝ, 0 < r → ∀ z, f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) ≠ 0 →
      z ∈ closedBall y (r * R) := by
    intro r hr z hz
    have hz' := hfR _ hz
    rw [liptsp_norm_blowUp y z hr, div_le_iff₀ hr] at hz'
    rw [mem_closedBall, dist_eq_norm, mul_comm]
    exact hz'
  have hFc : ∀ r : ℝ, Continuous fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) :=
    fun r => (map_continuous f).comp (by
      unfold Poincare.SimonGMT.Chapter03.blowUpMap
      fun_prop)
  -- The splitting estimate, for `0 < r < δ₀ / R`.
  have hbound : ∀ r ∈ Ioo (0 : ℝ) (δ₀ / R),
      ‖(∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' V.carrier,
          f z * V.mult (y + r • z) ∂(μHE[n] : Measure (Amb n ℓ))) -
        V.mult y * ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' N,
          f z ∂(μHE[n] : Measure (Amb n ℓ))‖ₑ ≤
      ENNReal.ofReal ((r ^ n)⁻¹) * (ENNReal.ofReal Cf *
        (∫⁻ z in closedBall y (r * R), ‖(V.carrier ∩ K).indicator V.mult z -
          (V.carrier ∩ K).indicator V.mult y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)).restrict N) +
        ENNReal.ofReal Cf * ((μHE[n] : Measure (Amb n ℓ)).withDensity
          fun z => ‖(V.carrier ∩ K).indicator V.mult z‖ₑ) (Nᶜ ∩ closedBall y (r * R))) := by
    rintro r ⟨hr, hrδ⟩
    have hBK : closedBall y (r * R) ⊆ K :=
      (closedBall_subset_closedBall ((lt_div_iff₀ hR).1 hrδ).le).trans hyK
    have hF0 : ∀ z, z ∉ closedBall y (r * R) →
        f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) = 0 := fun z hz => by
      by_contra h
      exact hz (hsupp r hr z h)
    have hFg : Integrable (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
        (V.carrier ∩ K).indicator V.mult z) (μHE[n] : Measure (Amb n ℓ)) :=
      hgi.bdd_mul (hFc r).aestronglyMeasurable (Eventually.of_forall fun z => hCf _)
    have hFN : IntegrableOn (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap y r z)) N
        (μHE[n] : Measure (Amb n ℓ)) :=
      Measure.integrableOn_of_bounded hNfin.ne (hFc r).aestronglyMeasurable
        (Eventually.of_forall fun z => hCf _)
    have hI := liptsp_blowUp_weighted_eq V K f y hr fun z hz => hF0 z fun hzB => hz (hBK hzB)
    have hJ : ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' N, f z
        ∂(μHE[n] : Measure (Amb n ℓ)) =
        (r ^ n)⁻¹ * ∫ z in N, f (Poincare.SimonGMT.Chapter03.blowUpMap y r z)
          ∂(μHE[n] : Measure (Amb n ℓ)) := by
      simpa only [mul_one] using liptsp_blowUp_setIntegral_eq n ℓ N f (fun _ => 1) y hr
    have hsplit := (integral_add_compl hNm hFg).symm
    have hdiff : ∫ z in N, f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
        ((V.carrier ∩ K).indicator V.mult z - (V.carrier ∩ K).indicator V.mult y)
          ∂(μHE[n] : Measure (Amb n ℓ)) =
        (∫ z in N, f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
          (V.carrier ∩ K).indicator V.mult z ∂(μHE[n] : Measure (Amb n ℓ))) -
        (∫ z in N, f (Poincare.SimonGMT.Chapter03.blowUpMap y r z)
          ∂(μHE[n] : Measure (Amb n ℓ))) * V.mult y := by
      rw [← integral_mul_const, ← integral_sub hFg.integrableOn (hFN.mul_const _), hgy]
      congr 1
      ext z
      ring
    have key : (∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' V.carrier,
          f z * V.mult (y + r • z) ∂(μHE[n] : Measure (Amb n ℓ))) -
        V.mult y * ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' N,
          f z ∂(μHE[n] : Measure (Amb n ℓ)) =
        (r ^ n)⁻¹ * ((∫ z in N, f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
            ((V.carrier ∩ K).indicator V.mult z - (V.carrier ∩ K).indicator V.mult y)
              ∂(μHE[n] : Measure (Amb n ℓ))) +
          ∫ z in Nᶜ, f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
            (V.carrier ∩ K).indicator V.mult z ∂(μHE[n] : Measure (Amb n ℓ))) := by
      rw [hI, hJ, hsplit, hdiff]
      ring
    have hE1 : ‖∫ z in N, f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
        ((V.carrier ∩ K).indicator V.mult z - (V.carrier ∩ K).indicator V.mult y)
          ∂(μHE[n] : Measure (Amb n ℓ))‖ₑ ≤
        ENNReal.ofReal Cf * ∫⁻ z in closedBall y (r * R), ‖(V.carrier ∩ K).indicator V.mult z -
          (V.carrier ∩ K).indicator V.mult y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)).restrict N := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_indicator measurableSet_closedBall]
      refine lintegral_mono fun z => ?_
      by_cases hz : z ∈ closedBall y (r * R)
      · rw [indicator_of_mem hz, enorm_mul]
        gcongr
        exact hfb _
      · rw [indicator_of_notMem hz, hF0 z hz, zero_mul, enorm_zero]
    have hE2 : ‖∫ z in Nᶜ, f (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
        (V.carrier ∩ K).indicator V.mult z ∂(μHE[n] : Measure (Amb n ℓ))‖ₑ ≤
        ENNReal.ofReal Cf * ((μHE[n] : Measure (Amb n ℓ)).withDensity
          fun z => ‖(V.carrier ∩ K).indicator V.mult z‖ₑ) (Nᶜ ∩ closedBall y (r * R)) := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [withDensity_apply _ (hNm.compl.inter measurableSet_closedBall),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, inter_comm Nᶜ (closedBall y (r * R)),
        ← Measure.restrict_restrict measurableSet_closedBall,
        ← lintegral_indicator measurableSet_closedBall]
      refine lintegral_mono fun z => ?_
      by_cases hz : z ∈ closedBall y (r * R)
      · rw [indicator_of_mem hz, enorm_mul]
        gcongr
        exact hfb _
      · rw [indicator_of_notMem hz, hF0 z hz, zero_mul, enorm_zero]
    have hrn : 0 ≤ (r ^ n)⁻¹ := inv_nonneg.2 (pow_nonneg hr.le n)
    rw [key, enorm_mul, Real.enorm_eq_ofReal hrn]
    gcongr
    exact (enorm_add_le _ _).trans (add_le_add hE1 hE2)
  -- Assemble the limits.
  have hmul : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun r : ℝ => r * R := by fun_prop
      exact (hc.tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hR
  have hω : 0 < unitBallVolume n := liptsp_unitBallVolume_pos n
  have hT1 : Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) *
      ((μHE[n] : Measure (Amb n ℓ)).withDensity
        fun z => ‖(V.carrier ∩ K).indicator V.mult z‖ₑ) (Nᶜ ∩ closedBall y (r * R)))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (hα.comp hmul)
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (unitBallVolume n * R ^ n) ≠ ⊤))
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : 0 < r := hr
    have hpos : 0 < unitBallVolume n * (r * R) ^ n := mul_pos hω (pow_pos (mul_pos hr' hR) n)
    simp only [Function.comp_apply]
    rw [ENNReal.div_eq_inv_mul, ← mul_assoc, ← ENNReal.ofReal_inv_of_pos hpos,
      ← ENNReal.ofReal_mul (mul_pos hω (pow_pos hR n)).le]
    congr 2
    rw [mul_pow]
    field_simp
  have hT2 : Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) *
      ∫⁻ z in closedBall y (r * R), ‖(V.carrier ∩ K).indicator V.mult z -
        (V.carrier ∩ K).indicator V.mult y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)).restrict N)
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (hγ'.comp hmul)
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (R ^ n) ≠ ⊤))
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : 0 < r := hr
    simp only [Function.comp_apply]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hR.le n)]
    congr 2
    rw [mul_pow]
    field_simp
  have hU : Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) * (ENNReal.ofReal Cf *
        (∫⁻ z in closedBall y (r * R), ‖(V.carrier ∩ K).indicator V.mult z -
          (V.carrier ∩ K).indicator V.mult y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)).restrict N) +
        ENNReal.ofReal Cf * ((μHE[n] : Measure (Amb n ℓ)).withDensity
          fun z => ‖(V.carrier ∩ K).indicator V.mult z‖ₑ) (Nᶜ ∩ closedBall y (r * R))))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (hT2.add hT1)
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal Cf ≠ ⊤))
    simp only [add_zero, mul_zero] at h
    refine h.congr' (Eventually.of_forall fun r => ?_)
    ring
  have hdiff : Tendsto (fun r : ℝ =>
      (∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' V.carrier,
        f z * V.mult (y + r • z) ∂(μHE[n] : Measure (Amb n ℓ))) -
      V.mult y * ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' N,
        f z ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
      (Eventually.of_forall fun r => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ₀ hR)] with r hr
    rw [edist_zero_right]
    exact hbound r hr
  have h := hdiff.add ((hP.2 f).const_mul (V.mult y))
  simp only [sub_add_cancel, zero_add] at h
  exact h

/-- **Weighted tangent planes on one chart** (Parts D–E): for `Hⁿ`-a.e. `y ∈ M ∩ N`, the
approximate tangent plane `T(y)` of `N` is the weighted approximate tangent plane of `(M, θ)`.
Localize to `K = B_{ε/2}(x) ⊆ U` around each point; there `g = θ 1_{M ∩ K}` is `Hⁿ`-integrable, so
Lebesgue differentiation (Besicovitch) applies to `g` and `Hⁿ ⌞ N`, and the Upper Density Theorem
applies to the finite measure `|g| Hⁿ` and the set `Nᶜ`. -/
theorem liptsp_weighted_ae_on_chart {n ℓ : ℕ} {U : Set (Amb n ℓ)} (hU : IsOpen U)
    (V : RectifiableVarifold n ℓ U) {N : Set (Amb n ℓ)} (hNm : MeasurableSet N)
    (hNfin : (μHE[n] : Measure (Amb n ℓ)) N < ⊤) {T : Amb n ℓ → Submodule ℝ (Amb n ℓ)}
    (hT : ∀ x ∈ N, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N x (T x)) :
    ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)), x ∈ V.carrier → x ∈ N →
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x
        (T x) := by
  have hS0 : (μHE[n] : Measure (Amb n ℓ)) {x | x ∈ V.carrier ∧ x ∈ N ∧
      ¬ Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x
        (T x)} = 0 := by
    refine measure_null_of_locally_null _ fun x hx => ?_
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x (V.carrier_subset hx.1)
    have hKU : closedBall x (ε / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεU
    refine ⟨_, inter_mem_nhdsWithin _ (ball_mem_nhds x (half_pos hε)), ?_⟩
    have hMK : NullMeasurableSet (V.carrier ∩ closedBall x (ε / 2))
        (μHE[n] : Measure (Amb n ℓ)) :=
      V.nullMeasurableSet_carrier.inter measurableSet_closedBall.nullMeasurableSet
    have hgi : Integrable ((V.carrier ∩ closedBall x (ε / 2)).indicator V.mult)
        (μHE[n] : Measure (Amb n ℓ)) :=
      (V.integrableOn_mult _ (isCompact_closedBall x _) hKU).integrable_indicator₀ hMK
    -- The Upper Density Theorem for `ν = |g| Hⁿ` on `Nᶜ`.
    have hνfin : ((μHE[n] : Measure (Amb n ℓ)).withDensity fun z =>
        ‖(V.carrier ∩ closedBall x (ε / 2)).indicator V.mult z‖ₑ) Nᶜ < ⊤ := by
      refine lt_of_le_of_lt (measure_mono (subset_univ _)) ?_
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact hgi.2
    have hUD := upperDensity_ne_zero_outside_hausdorff_null _ Nᶜ
      hNm.compl.nullMeasurableSet hνfin
    -- Lebesgue differentiation of `g` with respect to `Hⁿ ⌞ N`.
    have : IsFiniteMeasure ((μHE[n] : Measure (Amb n ℓ)).restrict N) :=
      isFiniteMeasure_restrict.2 hNfin.ne
    have hLeb := (Besicovitch.vitaliFamily
      ((μHE[n] : Measure (Amb n ℓ)).restrict N)).ae_tendsto_lintegral_enorm_sub_div
        (hgi.restrict (s := N)).locallyIntegrable
    rw [ae_restrict_iff' hNm] at hLeb
    rw [measure_eq_zero_iff_ae_notMem] at hUD ⊢
    filter_upwards [hLeb, hUD] with z hz1 hz2 hzu
    obtain ⟨⟨hzM, hzN, hzbad⟩, hzball⟩ := hzu
    apply hzbad
    have hzx : dist z x < ε / 2 := mem_ball.1 hzball
    have hδ₀ : 0 < ε / 2 - dist z x := sub_pos.2 hzx
    have hsub : closedBall z (ε / 2 - dist z x) ⊆ closedBall x (ε / 2) :=
      closedBall_subset_closedBall' (by linarith)
    refine liptsp_weighted_of_lebesgue_point V hNm hNfin (isCompact_closedBall x _) hKU hδ₀ hsub
      hzM (hT z hzN) ?_ ((hz1 hzN).comp (Besicovitch.tendsto_filterAt _ z))
    have hlim : limsup (fun s : ℝ => ((μHE[n] : Measure (Amb n ℓ)).withDensity fun w =>
        ‖(V.carrier ∩ closedBall x (ε / 2)).indicator V.mult w‖ₑ) (Nᶜ ∩ closedBall z s) /
        ENNReal.ofReal (unitBallVolume n * s ^ n)) (𝓝[>] 0) = 0 := by
      by_contra hne
      exact hz2 ⟨fun h => h hzN, hne⟩
    exact tendsto_of_le_liminf_of_limsup_le zero_le hlim.le
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hS0
  simp only [mem_ofPred_eq, not_imp] at hx
  exact ⟨hx.1, hx.2.1, hx.2.2⟩

/-- On `M` (where `θ > 0`) a weighted approximate tangent plane is unique (Simon Remark 1.5(1)),
so it is the plane chosen in `tangentProj`. -/
theorem liptsp_tangentProj_eq {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
    {x : Amb n ℓ} (hx : x ∈ V.carrier) {P : Submodule ℝ (Amb n ℓ)}
    (hP : Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x
      P) :
    V.tangentProj x = P.starProjection := by
  have h : ∃ Q : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x Q :=
    ⟨P, hP⟩
  have hcongr : ∀ A B : Submodule ℝ (Amb n ℓ), A = B → A.starProjection = B.starProjection := by
    rintro A B rfl
    rfl
  rw [RectifiableVarifold.tangentProj, dite_eq_left h]
  exact hcongr _ _ ((Classical.choose_spec h).unique (V.mult_pos x hx).ne' hP)

/-- Local finiteness (L): `μ_V(K) < ∞` for compact `K ⊆ U`. -/
theorem liptsp_weight_lt_top {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
    {K : Set (Amb n ℓ)} (hK : IsCompact K) (hKU : K ⊆ U) : V.weight K < ⊤ := by
  rw [RectifiableVarifold.weight, withDensity_apply _ hK.isClosed.measurableSet,
    Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm K V.carrier]
  exact (V.integrableOn_mult K hK hKU).lintegral_lt_top

/-- A two-sided squeeze in `[0, ∞]`: if, for every `ε > 0`, `Q` is eventually between `ofReal` of
two functions with limits in `[t / (1+ε)ⁿ, t (1+ε)ⁿ]`, then `Q → ofReal t`. -/
theorem liptsp_tendsto_of_squeeze {n : ℕ} {Q : ℝ → ℝ≥0∞} {t : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ (lo hi : ℝ → ℝ) (cl ch : ℝ), Tendsto lo (𝓝[>] 0) (𝓝 cl) ∧
      Tendsto hi (𝓝[>] 0) (𝓝 ch) ∧ t / (1 + ε) ^ n ≤ cl ∧ ch ≤ t * (1 + ε) ^ n ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (lo r) ≤ Q r ∧ Q r ≤ ENNReal.ofReal (hi r)) :
    Tendsto Q (𝓝[>] 0) (𝓝 (ENNReal.ofReal t)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hcont : Tendsto (fun ε : ℝ => ENNReal.ofReal (t / (1 + ε) ^ n)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal t)) := by
      apply ENNReal.tendsto_ofReal
      have h0 : Tendsto (fun ε : ℝ => t / (1 + ε) ^ n) (𝓝 0) (𝓝 (t / (1 + 0) ^ n)) :=
        tendsto_const_nhds.div ((tendsto_const_nhds.add tendsto_id).pow n) (by simp)
      rw [add_zero, one_pow, div_one] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    obtain ⟨ε, hεa, hε⟩ := ((hcont.eventually (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    obtain ⟨lo, hi, cl, ch, hlo, -, hcl, -, hev⟩ := h ε hε
    have hacl : a < ENNReal.ofReal cl := hεa.trans_le (ENNReal.ofReal_le_ofReal hcl)
    filter_upwards [hev, (ENNReal.tendsto_ofReal hlo).eventually (lt_mem_nhds hacl)]
      with r hr1 hr2
    exact hr2.trans_le hr1.1
  · intro b hb
    have hcont : Tendsto (fun ε : ℝ => ENNReal.ofReal (t * (1 + ε) ^ n)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal t)) := by
      apply ENNReal.tendsto_ofReal
      have h0 : Tendsto (fun ε : ℝ => t * (1 + ε) ^ n) (𝓝 0) (𝓝 (t * (1 + 0) ^ n)) :=
        tendsto_const_nhds.mul ((tendsto_const_nhds.add tendsto_id).pow n)
      rw [add_zero, one_pow, mul_one] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    obtain ⟨ε, hεb, hε⟩ := ((hcont.eventually (gt_mem_nhds hb)).and self_mem_nhdsWithin).exists
    obtain ⟨lo, hi, cl, ch, -, hhi, -, hch, hev⟩ := h ε hε
    have hchb : ENNReal.ofReal ch < b := (ENNReal.ofReal_le_ofReal hch).trans_lt hεb
    filter_upwards [hev, (ENNReal.tendsto_ofReal hhi).eventually (gt_mem_nhds hchb)]
      with r hr1 hr2
    exact hr1.2.trans_lt hr2

/-- **Density from a weighted tangent plane** (Part F, Simon Remark 1.8(2)): if `y ∈ M` and
`(M, θ)` has a weighted approximate tangent plane `P` at `y`, then
`μ_V(B_r(y)) / (ω_n rⁿ) → θ(y)`.  Squeeze `1_{B_r(y)}` between `φ(η_{y,r/(1+ε)})` and
`φ(η_{y,r})` for a cut-off `1_{B_1} ≤ φ ≤ 1_{B_{1+ε}}`, and use
`ω_n ≤ ∫_P φ ≤ ω_n (1+ε)ⁿ`. -/
theorem liptsp_hasDensity_of_weighted {n ℓ : ℕ} (hn : 1 ≤ n) {U : Set (Amb n ℓ)}
    (hU : IsOpen U) (V : RectifiableVarifold n ℓ U) {y : Amb n ℓ} (hyM : y ∈ V.carrier)
    {P : Submodule ℝ (Amb n ℓ)}
    (hW : Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult y
      P) :
    V.HasDensity y (V.mult y) := by
  have hω : 0 < unitBallVolume n := liptsp_unitBallVolume_pos n
  have hθ : 0 < V.mult y := V.mult_pos y hyM
  obtain ⟨r₁, hr₁, hr₁U⟩ := Metric.isOpen_iff.1 hU y (V.carrier_subset hyM)
  have hKU : closedBall y (r₁ / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hr₁)).trans hr₁U
  have hMK : NullMeasurableSet (V.carrier ∩ closedBall y (r₁ / 2))
      (μHE[n] : Measure (Amb n ℓ)) :=
    V.nullMeasurableSet_carrier.inter measurableSet_closedBall.nullMeasurableSet
  have hgi : Integrable ((V.carrier ∩ closedBall y (r₁ / 2)).indicator V.mult)
      (μHE[n] : Measure (Amb n ℓ)) :=
    (V.integrableOn_mult _ (isCompact_closedBall y _) hKU).integrable_indicator₀ hMK
  have hg0 : ∀ z, 0 ≤ (V.carrier ∩ closedBall y (r₁ / 2)).indicator V.mult z := fun z => by
    by_cases hz : z ∈ V.carrier ∩ closedBall y (r₁ / 2)
    · rw [indicator_of_mem hz]
      exact (V.mult_pos z hz.1).le
    · rw [indicator_of_notMem hz]
  -- `μ_V(B_s(y)) = ∫ ofReal (1_{B_s(y)} g) dHⁿ` for `s ≤ r₁ / 2`.
  have hwt : ∀ s, s ≤ r₁ / 2 → V.weight (closedBall y s) = ∫⁻ z, ENNReal.ofReal
      ((closedBall y s).indicator ((V.carrier ∩ closedBall y (r₁ / 2)).indicator V.mult) z)
        ∂(μHE[n] : Measure (Amb n ℓ)) := by
    intro s hs
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall,
      ← lintegral_indicator₀ (measurableSet_closedBall.nullMeasurableSet.inter
        V.nullMeasurableSet_carrier)]
    refine lintegral_congr fun z => ?_
    by_cases hzB : z ∈ closedBall y s
    · by_cases hzM : z ∈ V.carrier
      · rw [indicator_of_mem (Set.mem_inter hzB hzM), indicator_of_mem hzB,
          indicator_of_mem (Set.mem_inter hzM (closedBall_subset_closedBall hs hzB))]
      · rw [indicator_of_notMem (fun h : z ∈ closedBall y s ∩ V.carrier => hzM h.2),
          indicator_of_mem hzB,
          indicator_of_notMem (fun h : z ∈ V.carrier ∩ closedBall y (r₁ / 2) => hzM h.1),
          ENNReal.ofReal_zero]
    · rw [indicator_of_notMem (fun h : z ∈ closedBall y s ∩ V.carrier => hzB h.1),
        indicator_of_notMem hzB, ENNReal.ofReal_zero]
  refine liptsp_tendsto_of_squeeze (n := n) fun ε hε => ?_
  obtain ⟨φ, hφ01, hφ1, hφ0⟩ := liptsp_exists_cutoff (n := n) (ℓ := ℓ) hε
  have hε1 : 0 < 1 + ε := by linarith
  -- `ω_n ≤ ∫_P φ ≤ ω_n (1+ε)ⁿ`.
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hW.1
  have hφi : Integrable φ ((μHE[n] : Measure (Amb n ℓ)).restrict (P : Set (Amb n ℓ))) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hball : ∀ s : ℝ, 0 ≤ s → Integrable
      ((closedBall (0 : Amb n ℓ) s).indicator (1 : Amb n ℓ → ℝ))
      ((μHE[n] : Measure (Amb n ℓ)).restrict (P : Set (Amb n ℓ))) := fun s hs =>
    (integrableOn_const (by rw [liptsp_planeMeasure_closedBall hn hW.1 hs]; exact
      ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_closedBall
  have hPlo : unitBallVolume n ≤
      ∫ z in (P : Set (Amb n ℓ)), φ z ∂(μHE[n] : Measure (Amb n ℓ)) := by
    have hle : (closedBall (0 : Amb n ℓ) 1).indicator (1 : Amb n ℓ → ℝ) ≤ φ := fun z => by
      by_cases hz : z ∈ closedBall (0 : Amb n ℓ) 1
      · rw [indicator_of_mem hz, Pi.one_apply, hφ1 z (mem_closedBall_zero_iff.1 hz)]
      · rw [indicator_of_notMem hz]
        exact (hφ01 z).1
    have h := integral_mono (hball 1 zero_le_one) hφi hle
    rwa [integral_indicator_one measurableSet_closedBall, measureReal_def,
      liptsp_planeMeasure_closedBall hn hW.1 zero_le_one, one_pow, mul_one,
      ENNReal.toReal_ofReal hω.le] at h
  have hPhi : ∫ z in (P : Set (Amb n ℓ)), φ z ∂(μHE[n] : Measure (Amb n ℓ)) ≤
      unitBallVolume n * (1 + ε) ^ n := by
    have hle : (φ : Amb n ℓ → ℝ) ≤ (closedBall (0 : Amb n ℓ) (1 + ε)).indicator 1 := fun z => by
      by_cases hz : z ∈ closedBall (0 : Amb n ℓ) (1 + ε)
      · rw [indicator_of_mem hz, Pi.one_apply]
        exact (hφ01 z).2
      · rw [indicator_of_notMem hz, hφ0 z (by rwa [mem_closedBall_zero_iff, not_le] at hz)]
    have h := integral_mono hφi (hball (1 + ε) hε1.le) hle
    rwa [integral_indicator_one measurableSet_closedBall, measureReal_def,
      liptsp_planeMeasure_closedBall hn hW.1 hε1.le,
      ENNReal.toReal_ofReal (mul_nonneg hω.le (pow_nonneg hε1.le n))] at h
  -- The blow-up integrals `I(r) = ∫_{η_r(M)} φ θ(y + r·)`.
  have hφc : ∀ r : ℝ, Continuous fun z => φ (Poincare.SimonGMT.Chapter03.blowUpMap y r z) :=
    fun r => (map_continuous φ).comp (by
      unfold Poincare.SimonGMT.Chapter03.blowUpMap
      fun_prop)
  have hJi : ∀ r : ℝ, Integrable (fun z => φ (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
      (V.carrier ∩ closedBall y (r₁ / 2)).indicator V.mult z) (μHE[n] : Measure (Amb n ℓ)) :=
    fun r => hgi.bdd_mul (hφc r).aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hφ01 _).1]; exact (hφ01 _).2)
  have hJ0 : ∀ r : ℝ, ENNReal.ofReal (∫ z, φ (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
      (V.carrier ∩ closedBall y (r₁ / 2)).indicator V.mult z ∂(μHE[n] : Measure (Amb n ℓ))) =
      ∫⁻ z, ENNReal.ofReal (φ (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
        (V.carrier ∩ closedBall y (r₁ / 2)).indicator V.mult z)
        ∂(μHE[n] : Measure (Amb n ℓ)) := fun r =>
    ofReal_integral_eq_lintegral_ofReal (hJi r)
      (Eventually.of_forall fun z => mul_nonneg (hφ01 _).1 (hg0 z))
  -- `I(r) = r⁻ⁿ J(r)` whenever `φ ∘ η_r` vanishes off `B_{r₁/2}(y)`.
  have hIJ : ∀ r : ℝ, 0 < r → r * (1 + ε) ≤ r₁ / 2 →
      ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' V.carrier, φ z * V.mult (y + r • z)
        ∂(μHE[n] : Measure (Amb n ℓ)) =
      (r ^ n)⁻¹ * ∫ z, φ (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
        (V.carrier ∩ closedBall y (r₁ / 2)).indicator V.mult z ∂(μHE[n] : Measure (Amb n ℓ)) := by
    intro r hr hrK
    refine liptsp_blowUp_weighted_eq V _ φ y hr fun z hz => hφ0 _ ?_
    rw [liptsp_norm_blowUp y z hr, lt_div_iff₀ hr]
    rw [mem_closedBall, dist_eq_norm, not_le] at hz
    linarith
  refine ⟨fun r => (1 + ε)⁻¹ ^ n * (∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y (r / (1 + ε)) ''
      V.carrier, φ z * V.mult (y + (r / (1 + ε)) • z) ∂(μHE[n] : Measure (Amb n ℓ))) /
      unitBallVolume n,
    fun r => (∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' V.carrier,
      φ z * V.mult (y + r • z) ∂(μHE[n] : Measure (Amb n ℓ))) / unitBallVolume n,
    (1 + ε)⁻¹ ^ n * (V.mult y * ∫ z in (P : Set (Amb n ℓ)), φ z ∂(μHE[n] : Measure (Amb n ℓ))) /
      unitBallVolume n,
    V.mult y * (∫ z in (P : Set (Amb n ℓ)), φ z ∂(μHE[n] : Measure (Amb n ℓ))) / unitBallVolume n,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hdiv : Tendsto (fun r : ℝ => r / (1 + ε)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Continuous fun r : ℝ => r / (1 + ε) := by fun_prop
        exact (hc.tendsto' 0 0 (zero_div _)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact div_pos hr hε1
    exact (((hW.2 φ).comp hdiv).const_mul _).div_const _
  · exact (hW.2 φ).div_const _
  · rw [div_le_div_iff₀ (pow_pos hε1 n) hω]
    calc V.mult y * unitBallVolume n
        = (1 + ε)⁻¹ ^ n * (V.mult y * unitBallVolume n) * (1 + ε) ^ n := by
          rw [inv_pow]
          field_simp
      _ ≤ (1 + ε)⁻¹ ^ n * (V.mult y * ∫ z in (P : Set (Amb n ℓ)), φ z
            ∂(μHE[n] : Measure (Amb n ℓ))) * (1 + ε) ^ n := by
          gcongr
  · rw [div_le_iff₀ hω]
    calc V.mult y * (∫ z in (P : Set (Amb n ℓ)), φ z ∂(μHE[n] : Measure (Amb n ℓ)))
        ≤ V.mult y * (unitBallVolume n * (1 + ε) ^ n) := by gcongr
      _ = V.mult y * (1 + ε) ^ n * unitBallVolume n := by ring
  · filter_upwards [Ioo_mem_nhdsGT (show 0 < r₁ / 2 / (1 + ε) by positivity)] with r hr
    obtain ⟨hr0, hrK⟩ := hr
    have hrK' : r * (1 + ε) ≤ r₁ / 2 := ((lt_div_iff₀ hε1).1 hrK).le
    have hrr : r ≤ r₁ / 2 := le_trans (le_mul_of_one_le_right hr0.le (by linarith)) hrK'
    have hr'0 : 0 < r / (1 + ε) := div_pos hr0 hε1
    have hr'K : r / (1 + ε) * (1 + ε) ≤ r₁ / 2 := by
      rw [div_mul_cancel₀ _ hε1.ne']
      exact hrr
    have hωr : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr0 n)
    constructor
    · -- lower bound
      rw [hIJ _ hr'0 hr'K, hwt r hrr]
      have hlo : ENNReal.ofReal (∫ z, φ (Poincare.SimonGMT.Chapter03.blowUpMap y (r / (1 + ε)) z) *
          (V.carrier ∩ closedBall y (r₁ / 2)).indicator V.mult z ∂(μHE[n] : Measure (Amb n ℓ))) ≤
          ∫⁻ z, ENNReal.ofReal ((closedBall y r).indicator
            ((V.carrier ∩ closedBall y (r₁ / 2)).indicator V.mult) z)
            ∂(μHE[n] : Measure (Amb n ℓ)) := by
        rw [hJ0]
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ closedBall y r
        · rw [indicator_of_mem hz]
          exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hg0 z) (hφ01 _).2)
        · rw [hφ0 _ ?_, zero_mul, ENNReal.ofReal_zero]
          · exact zero_le
          · rw [liptsp_norm_blowUp y z hr'0, lt_div_iff₀ hr'0, mul_comm, div_mul_cancel₀ _ hε1.ne']
            rw [mem_closedBall, dist_eq_norm, not_le] at hz
            exact hz
      refine le_trans (le_of_eq ?_) (ENNReal.div_le_div_right hlo _)
      rw [← ENNReal.ofReal_div_of_pos hωr]
      congr 1
      have hscal : (1 + ε)⁻¹ ^ n * ((r / (1 + ε)) ^ n)⁻¹ = (r ^ n)⁻¹ := by
        rw [div_pow, inv_div, inv_pow, ← mul_div_assoc, inv_mul_cancel₀ (pow_ne_zero n hε1.ne'),
          one_div]
      rw [← mul_assoc, hscal, inv_mul_eq_div, div_div, mul_comm (r ^ n)]
    · -- upper bound
      rw [hIJ r hr0 hrK', hwt r hrr]
      have hhi : ∫⁻ z, ENNReal.ofReal ((closedBall y r).indicator
            ((V.carrier ∩ closedBall y (r₁ / 2)).indicator V.mult) z)
            ∂(μHE[n] : Measure (Amb n ℓ)) ≤
          ENNReal.ofReal (∫ z, φ (Poincare.SimonGMT.Chapter03.blowUpMap y r z) *
            (V.carrier ∩ closedBall y (r₁ / 2)).indicator V.mult z
              ∂(μHE[n] : Measure (Amb n ℓ))) := by
        rw [hJ0]
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ closedBall y r
        · rw [indicator_of_mem hz, hφ1 _ ?_, one_mul]
          rw [liptsp_norm_blowUp y z hr0, div_le_one hr0]
          rw [mem_closedBall, dist_eq_norm] at hz
          exact hz
        · rw [indicator_of_notMem hz, ENNReal.ofReal_zero]
          exact zero_le
      refine le_trans (ENNReal.div_le_div_right hhi _) (le_of_eq ?_)
      rw [← ENNReal.ofReal_div_of_pos hωr]
      congr 1
      field_simp

/-- `‖p_x‖ ≤ 1`: `tangentProj x` is `0` or an orthogonal projection. -/
theorem liptsp_norm_tangentProj_le {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
    (x : Amb n ℓ) : ‖V.tangentProj x‖ ≤ 1 := by
  unfold RectifiableVarifold.tangentProj
  split_ifs
  · exact Submodule.starProjection_norm_le _
  · simp

/-- `|A − B|² ≤ 4 (n + ℓ)` when `‖A‖, ‖B‖ ≤ 1` (each of the `n + ℓ` columns has norm `≤ 2`). -/
theorem liptsp_hsNormSq_sub_le {n ℓ : ℕ} (A B : Amb n ℓ →L[ℝ] Amb n ℓ) (hA : ‖A‖ ≤ 1)
    (hB : ‖B‖ ≤ 1) : ‖hsNormSq (A - B)‖ ≤ 4 * ((n + ℓ : ℕ) : ℝ) := by
  have h0 : 0 ≤ hsNormSq (A - B) := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.norm_of_nonneg h0]
  unfold hsNormSq
  calc ∑ i : Fin (n + ℓ), ‖(A - B) (EuclideanSpace.single i 1)‖ ^ 2
      ≤ ∑ _i : Fin (n + ℓ), (4 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : ‖(A - B) (EuclideanSpace.single i (1 : ℝ))‖ ≤ 2 := by
          calc ‖(A - B) (EuclideanSpace.single i (1 : ℝ))‖
              ≤ ‖A - B‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := (A - B).le_opNorm _
            _ ≤ 2 * 1 := by
                gcongr
                · exact (norm_sub_le A B).trans (by linarith)
                · simp
            _ = 2 := mul_one 2
        nlinarith [norm_nonneg ((A - B) (EuclideanSpace.single i (1 : ℝ)))]
    _ = 4 * ((n + ℓ : ℕ) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- `A ↦ |A − B|²` is continuous. -/
theorem liptsp_continuous_hsNormSq_sub {n ℓ : ℕ} (B : Amb n ℓ →L[ℝ] Amb n ℓ) :
    Continuous fun A : Amb n ℓ →L[ℝ] Amb n ℓ => hsNormSq (A - B) := by
  unfold hsNormSq
  exact continuous_finsetSum _ fun i _ =>
    (((continuous_id.sub continuous_const).clm_apply continuous_const).norm).pow 2

/-- **The parent statement from a chart cover** (Parts D–H).  Given Borel `N_k` of finite
`Hⁿ`-measure covering `M` up to an `Hⁿ`-null set, with approximate tangent planes `T_k(x)` at every
`x ∈ N_k` depending continuously on `x ∈ N_k`, the conclusions (a)–(c) hold: `T_k(x)` is the
weighted plane at `μ_V`-a.e. `x ∈ N_k`, so `p_x = p_{T_k(x)}` there (continuous on `N_k`, giving
(a)), `|p_x − p_T|² ≤ 4(n+ℓ)` with `μ_V(K) < ∞` (giving (b)), and Part F gives the density. -/
theorem liptsp_of_chart_cover (n ℓ : ℕ) (hn : 1 ≤ n) (U : Set (Amb n ℓ)) (hU : IsOpen U)
    (V : RectifiableVarifold n ℓ U) (N : ℕ → Set (Amb n ℓ))
    (T : ℕ → Amb n ℓ → Submodule ℝ (Amb n ℓ)) (hNm : ∀ k, MeasurableSet (N k))
    (hNfin : ∀ k, (μHE[n] : Measure (Amb n ℓ)) (N k) < ⊤)
    (hTc : ∀ k, ContinuousOn (fun x => (T k x).starProjection) (N k))
    (hTt : ∀ k, ∀ x ∈ N k,
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (N k) x (T k x))
    (hcov : (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ ⋃ k, N k) = 0) :
    AEStronglyMeasurable V.tangentProj V.weight ∧
      (∀ (T₀ : Submodule ℝ (Amb n ℓ)) (K : Set (Amb n ℓ)), IsCompact K → K ⊆ U →
        IntegrableOn (fun x => hsNormSq (V.tangentProj x - T₀.starProjection)) K V.weight) ∧
      ∀ᵐ x ∂V.weight, (∃ T₀ : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T₀ = n ∧
        V.tangentProj x = T₀.starProjection) ∧ V.HasDensity x (V.mult x) := by
  have hμH : V.weight ≪ (μHE[n] : Measure (Amb n ℓ)) :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hμM : ∀ᵐ x ∂V.weight, x ∈ V.carrier :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  have hcovμ : ∀ᵐ x ∂V.weight, x ∉ V.carrier \ ⋃ k, N k :=
    hμH.ae_le (measure_eq_zero_iff_ae_notMem.1 hcov)
  have hW : ∀ k, ∀ᵐ x ∂V.weight, x ∈ V.carrier → x ∈ N k →
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x
        (T k x) :=
    fun k => hμH.ae_le (liptsp_weighted_ae_on_chart hU V (hNm k) (hNfin k) (hTt k))
  have hgood : ∀ᵐ x ∂V.weight, x ∈ V.carrier ∧ (∃ k, x ∈ N k) ∧ ∀ k, x ∈ N k →
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x
        (T k x) := by
    filter_upwards [hμM, hcovμ, ae_all_iff.2 hW] with x hxM hxcov hxW
    refine ⟨hxM, ?_, fun k hk => hxW k hxM hk⟩
    by_contra h
    exact hxcov ⟨hxM, fun hx => h (mem_iUnion.1 hx)⟩
  -- (a): on each `N_k`, `p_x = p_{T_k(x)}` a.e., which is continuous on the Borel set `N_k`.
  have ha : AEStronglyMeasurable V.tangentProj V.weight := by
    have hrestrict : V.weight.restrict (⋃ k, N k) = V.weight :=
      Measure.restrict_eq_self_of_ae_mem (by
        filter_upwards [hgood] with x hx
        exact mem_iUnion.2 hx.2.1)
    rw [← hrestrict, aestronglyMeasurable_iUnion_iff]
    intro k
    refine ((hTc k).aestronglyMeasurable (hNm k)).congr ?_
    rw [EventuallyEq, ae_restrict_iff' (hNm k)]
    filter_upwards [hgood] with x hx hxN
    exact (liptsp_tangentProj_eq V hx.1 (hx.2.2 k hxN)).symm
  refine ⟨ha, fun T₀ K hK hKU => ?_, ?_⟩
  · -- (b): a bounded measurable integrand on a set of finite `μ_V`-measure.
    exact Measure.integrableOn_of_bounded (liptsp_weight_lt_top V hK hKU).ne
      ((liptsp_continuous_hsNormSq_sub T₀.starProjection).comp_aestronglyMeasurable ha)
      (Eventually.of_forall fun x => liptsp_hsNormSq_sub_le _ _ (liptsp_norm_tangentProj_le V x)
        (Submodule.starProjection_norm_le _))
  · -- (c): uniqueness of the weighted plane on `M`, and Part F.
    filter_upwards [hgood] with x hx
    obtain ⟨k, hk⟩ := hx.2.1
    have hw := hx.2.2 k hk
    exact ⟨⟨T k x, hw.1, liptsp_tangentProj_eq V hx.1 hw⟩,
      liptsp_hasDensity_of_weighted hn hU V hx.1 hw⟩

/-- **Tangent structure of a rectifiable varifold** (fact (F1) of `lipschitz_approximation`; Simon
Ch. 3, Theorem 1.9 with Remarks 1.8(1),(2); Ch. 4, 1.3).  For `n ≥ 1` and `V = v(M, θ)` in the open
set `U`: (a) `x ↦ p_{T_x M}` is `μ_V`-a.e. strongly measurable; (b) `|p_{T_x M} − p_T|²` is
`μ_V`-integrable on every compact `K ⊆ U`; (c) for `μ_V`-a.e. `x`, `p_{T_x M}` is the projection onto
an `n`-plane and `Θⁿ(μ_V, x) = θ(x)`.  Parts A–C of the proof (the chart cover with continuous
approximate tangent planes) are `lipts_rectifiable_tangent_chart_cover`; Parts D–H are
`liptsp_of_chart_cover`. -/
theorem lip_approx_tangent_structure : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight ∧ (∀ (T : Submodule ℝ (Amb n ℓ)) (K : Set (Amb n ℓ)), IsCompact K → K ⊆ U → IntegrableOn (fun x => hsNormSq (V.tangentProj x - T.starProjection)) K V.weight) ∧ ∀ᵐ x ∂V.weight, (∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ V.tangentProj x = T.starProjection) ∧ V.HasDensity x (V.mult x) := by
  intro n ℓ hn U hU V
  obtain ⟨N, T, hNm, hNfin, hTc, hTt, hcov⟩ :=
    Submission.lipts_rectifiable_tangent_chart_cover n ℓ hn V.carrier V.countablyRectifiable
  exact liptsp_of_chart_cover n ℓ hn U hU V N T hNm hNfin hTc hTt hcov

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
