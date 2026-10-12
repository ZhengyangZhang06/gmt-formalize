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
