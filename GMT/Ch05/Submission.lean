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
import Poincare.SimonGMT.Chapter04.LpAnnular
import Poincare.SimonGMT.Chapter04.LpLowerDensity
import Poincare.SimonGMT.Chapter04.WeightedBlowUp

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

/-- **Monotonicity consequences of 2.3** (Simon Ch. 4, 4.1–4.10, with the corrected
coefficient `κ = (p-n)/(4p)` in 4.2).  Put `Λ = 4pδ/(p-n) = δ/κ ≤ 1`.  Restricted to `B̆_ρ(0)`,
`V` is a SimonGMT Chapter 4 rectifiable varifold: its carrier is a Borel `M' ⊆ M ∩ B̆_ρ(0)` with
`Hⁿ((M ∩ B̆_ρ(0)) \ M') = 0`, its tangent planes are the weighted approximate tangent planes
of `V` (`any_radius_tangent_ae`), which are also unweighted approximate tangent planes of `M'`
at `Hⁿ`-a.e. point of `M'` (Lebesgue points of `θ` for `Hⁿ ⌞ M'`, Simon Ch. 3, Remark 1.8(1)),
and its first variation in `B̆_ρ(0)` is that of `V`.  The corrected annular identity 4.7
(`exists_lpAnnularCorrection_of_memLp`) then gives (M1) from the monotonicity of
`Φ(t) = F(t) t⁻ⁿ μ(B_t(y)) + F(t) - 1`, (M2) from `ω_n Θ(y) ≤ Φ(s)` and `Θ ≥ 1` on the
support (`one_le_stationaryDensityReal_of_mem_support_lp`), and (M3) from the annular identity
at `0` and monotone convergence over annuli exhausting `B̆_ρ(0) \ {0}`. -/
theorem any_radius_monotonicity_bounds : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ (p - n) / (4 * p) → V.AllardHypotheses H p δ ρ → (∀ (y : Amb n ℓ) (R s r : ℝ), 0 < s → s ≤ r → r < R → closedBall y R ⊆ closedBall 0 ρ → (V.weight (closedBall y s)).toReal / s ^ n ≤ Real.exp (2 * (4 * p * δ / (p - n))) * ((V.weight (closedBall y r)).toReal / r ^ n) + 2 * Real.exp (4 * p * δ / (p - n)) * (4 * p * δ / (p - n))) ∧ (∀ y ∈ V.support, ∀ R s : ℝ, 0 < s → s < R → closedBall y R ⊆ closedBall 0 ρ → Real.exp (-(4 * p * δ / (p - n))) * (unitBallVolume n - 4 * p * δ / (p - n)) * s ^ n ≤ (V.weight (closedBall y s)).toReal) ∧ ∫⁻ x in ball (0 : Amb n ℓ) ρ, ENNReal.ofReal (‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ∂V.weight ≤ ENNReal.ofReal (Real.exp (4 * p * δ / (p - n)) * (Real.exp (4 * p * δ / (p - n)) * (1 + δ) * unitBallVolume n + 4 * p * δ / (p - n) - unitBallVolume n)) := by
  intro n ℓ hn p hp U hU V H δ ρ hδ hδκ hAllard
  obtain ⟨htan, htanm, -⟩ := Submission.any_radius_tangent_ae n ℓ hn U hU V
  obtain ⟨hρ, hH, hθ1, h0supp, hballU, hmass, hLpscale⟩ := hAllard
  -- constants
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hpn : 0 < p - n := sub_pos.mpr hp
  set Λ : ℝ := 4 * p * δ / (p - n) with hΛdef
  have hΛpos : 0 < Λ := by positivity
  have hΛ1 : Λ ≤ 1 := by
    rw [hΛdef, div_le_one hpn]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * p)).mp hδκ
    linarith
  have hκΛ : Poincare.SimonGMT.Chapter04.RectifiableVarifold.lpMeanCurvatureKappa n p * Λ = δ := by
    simp only [Poincare.SimonGMT.Chapter04.RectifiableVarifold.lpMeanCurvatureKappa, hΛdef]
    field_simp
  set ω : ℝ := unitBallVolume n with hωdef
  have hωpos : 0 < ω := div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by positivity))
  have hω' : (Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ)).toReal = ω := by
    rw [Poincare.SimonGMT.Chapter01.realUnitBallVolume_eq]
    exact ENNReal.toReal_ofReal hωpos.le
  -- notation
  set μ : Measure (Amb n ℓ) := V.weight with hμdef
  set W : Set (Amb n ℓ) := ball (0 : Amb n ℓ) ρ with hWdef
  have hWo : IsOpen W := isOpen_ball
  have hWU : W ⊆ U := ball_subset_closedBall.trans hballU
  have hWcb : W ⊆ closedBall (0 : Amb n ℓ) ρ := ball_subset_closedBall
  have hμρ : μ (closedBall (0 : Amb n ℓ) ρ) < ∞ := hmass.trans_lt ENNReal.ofReal_lt_top
  have hμW : μ W < ∞ := (measure_mono hWcb).trans_lt hμρ
  -- the carrier and the weight
  have hMnull : NullMeasurableSet V.carrier (μHE[n] : Measure (Amb n ℓ)) :=
    V.nullMeasurableSet_carrier
  have hgae : AEMeasurable (fun x => ENNReal.ofReal (V.mult x))
      ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) := V.aemeasurable_mult.ennreal_ofReal
  have hμeq : μ = ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).withDensity
      (fun x => ENNReal.ofReal (V.mult x)) := rfl
  have hμac : μ ≪ (μHE[n] : Measure (Amb n ℓ)) := by
    rw [hμeq]
    exact (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hμM : ∀ᵐ x ∂μ, x ∈ V.carrier := by
    rw [hμeq]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem₀ hMnull)
  obtain ⟨M', hM'sub, hM'meas, hM'ae⟩ :=
    (hMnull.inter measurableSet_ball.nullMeasurableSet).exists_measurable_subset_ae_eq
  have hM'M : M' ⊆ V.carrier := hM'sub.trans inter_subset_left
  have hM'W : M' ⊆ W := hM'sub.trans inter_subset_right
  -- θ ≥ 1 on the carrier
  have hθ1H : ∀ᵐ x ∂((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier), 1 ≤ V.mult x := by
    have h := hθ1
    rw [hμeq, ae_withDensity_iff' hgae] at h
    filter_upwards [h, ae_restrict_mem₀ hMnull] with x hx hxM
    exact hx (ENNReal.ofReal_pos.mpr (V.mult_pos x hxM)).ne'
  set ν : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)).restrict M' with hνdef
  have hνle' : ν ≤ (μHE[n] : Measure (Amb n ℓ)).restrict V.carrier :=
    Measure.restrict_mono hM'M le_rfl
  have hθ1ν : ∀ᵐ x ∂ν, 1 ≤ V.mult x := ae_mono hνle' hθ1H
  -- the weight restricted to `W`
  have hμW_eq : μ.restrict W = ν.withDensity (fun x => ENNReal.ofReal (V.mult x)) := by
    have h1 : μ.restrict W = μ.restrict M' := by
      apply Measure.restrict_congr_set
      have h2 : M' =ᵐ[μ] (V.carrier ∩ W : Set (Amb n ℓ)) := hμac.ae_eq hM'ae
      have h3 : (V.carrier ∩ W : Set (Amb n ℓ)) =ᵐ[μ] W := by
        filter_upwards [hμM] with x hx
        simp [hx]
      exact (h2.trans h3).symm
    rw [h1, hμeq, restrict_withDensity hM'meas, Measure.restrict_restrict hM'meas,
      inter_eq_left.mpr hM'M]
  have hνle : ν ≤ μ.restrict W := by
    rw [hμW_eq]
    conv_lhs => rw [← withDensity_one (μ := ν)]
    apply withDensity_mono
    filter_upwards [hθ1ν] with x hx
    simpa using ENNReal.ofReal_le_ofReal hx
  have hνfin : (μHE[n] : Measure (Amb n ℓ)) M' < ∞ := by
    have := hνle univ
    rw [hνdef, Measure.restrict_apply_univ, Measure.restrict_apply_univ] at this
    exact this.trans_lt hμW
  have hθint : IntegrableOn V.mult M' (μHE[n] : Measure (Amb n ℓ)) :=
    (V.integrableOn_mult _ (isCompact_closedBall 0 ρ) hballU).mono_set
      (subset_inter hM'M (hM'W.trans hWcb))
  -- change of variables for blow-ups
  have hcv : ∀ (x : Amb n ℓ) {r : ℝ}, 0 < r → ∀ (S : Set (Amb n ℓ)) (h : Amb n ℓ → ℝ),
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, h y ∂(μHE[n] : Measure (Amb n ℓ)) =
        r⁻¹ ^ n * ∫ z in S, h (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
          ∂(μHE[n] : Measure (Amb n ℓ)) := by
    intro x r hr S h
    let b := Poincare.SimonGMT.Chapter04.blowUpHomeomorph x hr
    have hi := b.symm.measurableEmbedding.integral_map
      (μ := (μHE[n] : Measure (Amb n ℓ)).restrict
        (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S)) (fun z ↦ h (b z))
    rw [Poincare.SimonGMT.Chapter04.map_inverse_blowUp_carrier x hr S, integral_smul_measure,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_pos.mpr hr).le, smul_eq_mul] at hi
    simp only [Homeomorph.apply_symm_apply] at hi
    simpa only [b, Poincare.SimonGMT.Chapter04.blowUpHomeomorph_apply] using hi.symm
  have hmemb : ∀ (x : Amb n ℓ) {r : ℝ}, 0 < r → ∀ (A : ℝ) (z : Amb n ℓ),
      Poincare.SimonGMT.Chapter03.blowUpMap x r z ∈ closedBall (0 : Amb n ℓ) A ↔
        z ∈ closedBall x (r * A) := by
    intro x r hr A z
    simp only [mem_closedBall, dist_eq_norm, sub_zero, Poincare.SimonGMT.Chapter03.blowUpMap,
      norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
    rw [← div_eq_inv_mul, div_le_iff₀ hr, mul_comm r A]
  -- weighted approximate tangents of `V` are unweighted approximate tangents of `M'`
  -- (Lebesgue points of `θ` for `ν = Hⁿ ⌞ M'`, Simon Ch. 3, Remark 1.8(1))
  have hbr : ∀ᵐ x ∂ν, ∀ P : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P →
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n M' x P := by
    have : IsFiniteMeasure ν := ⟨by rw [hνdef, Measure.restrict_apply_univ]; exact hνfin⟩
    have hθν : Integrable V.mult ν := hθint
    have hLeb : ∀ᵐ x ∂ν, Tendsto (fun s => ⨍ z in closedBall x s, ‖V.mult z - V.mult x‖ ∂ν)
        (𝓝[>] 0) (𝓝 0) := by
      filter_upwards [(Besicovitch.vitaliFamily ν).ae_tendsto_average_norm_sub
        hθν.locallyIntegrable] with x hx
      exact hx.comp (Besicovitch.tendsto_filterAt ν x)
    filter_upwards [hLeb, ae_restrict_mem hM'meas] with x hxLeb hxM' P hP
    have hxM : x ∈ V.carrier := (hM'sub hxM').1
    have hxW : x ∈ W := (hM'sub hxM').2
    have ha : 0 < V.mult x := V.mult_pos x hxM
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWo x hxW
    have hcbW : closedBall x (ε / 2) ⊆ W :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεW
    -- weighted blow-up integrals as integrals against `ν`
    have hweighted : ∀ (g : Amb n ℓ → ℝ) (A r : ℝ), 0 < r → closedBall x (r * A) ⊆ W →
        (∀ y, y ∉ closedBall (0 : Amb n ℓ) A → g y = 0) →
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier, g y * V.mult (x + r • y)
            ∂(μHE[n] : Measure (Amb n ℓ)) =
          r⁻¹ ^ n * ∫ z, g (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z ∂ν := by
      intro g A r hr hball hg
      rw [hcv x hr V.carrier]
      congr 1
      have h1 : ∀ z : Amb n ℓ, x + r • Poincare.SimonGMT.Chapter03.blowUpMap x r z = z := by
        intro z
        simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr.ne']
      simp_rw [h1]
      set F : Amb n ℓ → ℝ := fun z => g (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z
        with hF
      have hind : W.indicator F = F := by
        funext z
        by_cases hz : z ∈ W
        · simp [hz]
        · rw [indicator_of_notMem hz]
          have hz' : z ∉ closedBall x (r * A) := fun h => hz (hball h)
          have : Poincare.SimonGMT.Chapter03.blowUpMap x r z ∉ closedBall (0 : Amb n ℓ) A := by
            rwa [hmemb x hr]
          simp [hF, hg _ this]
      calc ∫ z in V.carrier, F z ∂(μHE[n] : Measure (Amb n ℓ))
          = ∫ z in V.carrier, W.indicator F z ∂(μHE[n] : Measure (Amb n ℓ)) := by rw [hind]
        _ = ∫ z in V.carrier ∩ W, F z ∂(μHE[n] : Measure (Amb n ℓ)) :=
            setIntegral_indicator hWo.measurableSet
        _ = ∫ z in M', F z ∂(μHE[n] : Measure (Amb n ℓ)) := setIntegral_congr_set hM'ae.symm
    -- unweighted blow-up integrals as integrals against `ν`
    have hunweighted : ∀ (g : Amb n ℓ → ℝ) (r : ℝ), 0 < r →
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M', g y
            ∂(μHE[n] : Measure (Amb n ℓ)) =
          r⁻¹ ^ n * ∫ z, g (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂ν := by
      intro g r hr
      exact hcv x hr M' g
    -- the mass bound `s⁻ⁿ ν(B_s(x)) ≤ C`
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (0 : ℝ), s⁻¹ ^ n * ν.real (closedBall x s) ≤ C := by
      let c := Poincare.SimonGMT.Chapter04.tangentDensityCutoff (E := Amb n ℓ) 1 one_pos
      have hlim := hP.2 c
      refine ⟨V.mult x * ∫ y in (P : Set (Amb n ℓ)), c y ∂(μHE[n] : Measure (Amb n ℓ)) + 1, ?_⟩
      filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_one _)),
        Ioc_mem_nhdsGT (show (0 : ℝ) < ε / 4 by positivity), self_mem_nhdsWithin] with s hs hs4 hs0
      refine le_trans ?_ hs.le
      have hs0' : (0 : ℝ) < s := hs0
      have hball2 : closedBall x (s * 2) ⊆ W :=
        (closedBall_subset_closedBall (by linarith [hs4.2])).trans hcbW
      rw [hweighted c 2 s hs0' hball2 (fun y hy => by
        apply Poincare.SimonGMT.Chapter04.tangentDensityCutoff_eq_zero
        norm_num; simpa using hy)]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_pos.mpr hs0').le n)
      rw [← integral_indicator_one measurableSet_closedBall]
      apply integral_mono_ae
      · exact (integrable_const (1 : ℝ)).indicator measurableSet_closedBall
      · refine hθν.bdd_mul (c := 1) ?_ ?_
        · exact (c.continuous.comp (by unfold Poincare.SimonGMT.Chapter03.blowUpMap; fun_prop)
            ).aestronglyMeasurable
        · filter_upwards with z
          have := Poincare.SimonGMT.Chapter04.tangentDensityCutoff_mem_Icc (E := Amb n ℓ)
            one_pos (Poincare.SimonGMT.Chapter03.blowUpMap x s z)
          rw [Real.norm_of_nonneg this.1]
          exact this.2
      · filter_upwards [hθ1ν] with z hz
        have hc := Poincare.SimonGMT.Chapter04.tangentDensityCutoff_mem_Icc (E := Amb n ℓ)
          one_pos (Poincare.SimonGMT.Chapter03.blowUpMap x s z)
        by_cases hzb : z ∈ closedBall x s
        · rw [indicator_of_mem hzb]
          have : c (Poincare.SimonGMT.Chapter03.blowUpMap x s z) = 1 := by
            apply Poincare.SimonGMT.Chapter04.tangentDensityCutoff_eq_one
            rw [hmemb x hs0', mul_one]
            exact hzb
          simp only [Pi.one_apply, this, one_mul]
          exact hz
        · rw [indicator_of_notMem hzb]
          exact mul_nonneg hc.1 (by linarith)
    -- now the convergence
    refine ⟨hP.1, fun f => ?_⟩
    obtain ⟨A₁, hA₁⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
    set A₀ : ℝ := max A₁ 1 with hA₀
    have hA₀pos : 0 < A₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hfA : ∀ y, y ∉ closedBall (0 : Amb n ℓ) A₀ → f y = 0 := by
      intro y hy
      apply image_eq_zero_of_notMem_tsupport
      intro hy'
      exact hy ((closedBall_subset_closedBall (le_max_left _ _)) (hA₁ hy'))
    obtain ⟨Cf, hCf⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    set L := ∫ y in (P : Set (Amb n ℓ)), f y ∂(μHE[n] : Measure (Amb n ℓ)) with hL
    set Un : ℝ → ℝ := fun r => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M', f y
      ∂(μHE[n] : Measure (Amb n ℓ)) with hUn
    set Wt : ℝ → ℝ := fun r => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' V.carrier,
      f y * V.mult (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ)) with hWt
    have hWtlim : Tendsto Wt (𝓝[>] 0) (𝓝 (V.mult x * L)) := hP.2 f
    have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
    have hscale : Tendsto (fun r : ℝ => r * A₀) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).mul_const A₀)
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos hr hA₀pos
    have havg := hxLeb.comp hscale
    have hCev := hscale.eventually hC
    have hdiff : Tendsto (fun r => V.mult x * Un r - Wt r) (𝓝[>] 0) (𝓝 0) := by
      apply squeeze_zero_norm' (a := fun r =>
        Cf * A₀ ^ n * C * ⨍ z in closedBall x (r * A₀), ‖V.mult z - V.mult x‖ ∂ν)
      · filter_upwards [hCev, self_mem_nhdsWithin,
          Ioc_mem_nhdsGT (show (0 : ℝ) < ε / 2 / A₀ by positivity)] with r hrC hr0 hrε
        have hr : (0 : ℝ) < r := hr0
        have hrA : r * A₀ ≤ ε / 2 := by
          have := hrε.2
          rwa [le_div_iff₀ hA₀pos] at this
        have hball : closedBall x (r * A₀) ⊆ W :=
          (closedBall_subset_closedBall hrA).trans hcbW
        have hfm : AEStronglyMeasurable
            (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) ν :=
          (f.continuous.comp (by unfold Poincare.SimonGMT.Chapter03.blowUpMap; fun_prop)
            ).aestronglyMeasurable
        have hfb : ∀ᵐ z ∂ν, ‖f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)‖ ≤ Cf :=
          Eventually.of_forall fun z => hCf _
        have hi1 : Integrable (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) ν :=
          Integrable.of_bound hfm Cf hfb
        have hi2 : Integrable
            (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z) ν :=
          hθν.bdd_mul hfm hfb
        have hUnr : Un r = r⁻¹ ^ n * ∫ z, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂ν :=
          hunweighted f r hr
        have hWtr : Wt r = r⁻¹ ^ n *
            ∫ z, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * V.mult z ∂ν :=
          hweighted f A₀ r hr hball hfA
        have heq : V.mult x * Un r - Wt r = r⁻¹ ^ n *
            ∫ z, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (V.mult x - V.mult z) ∂ν := by
          rw [hUnr, hWtr, ← mul_assoc, mul_comm (V.mult x), mul_assoc, ← mul_sub,
            ← integral_const_mul, ← integral_sub (hi1.const_mul _) hi2]
          congr 1
          apply integral_congr_ae
          filter_upwards with z
          ring
        set B := closedBall x (r * A₀) with hB
        have hbound :
            ‖∫ z, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (V.mult x - V.mult z) ∂ν‖ ≤
              ∫ z, Cf * B.indicator (fun z => ‖V.mult z - V.mult x‖) z ∂ν := by
          apply norm_integral_le_of_norm_le
          · exact (((hθν.sub (integrable_const (V.mult x))).norm).indicator
              measurableSet_closedBall).const_mul Cf
          · filter_upwards with z
            by_cases hz : z ∈ B
            · rw [indicator_of_mem hz, norm_mul]
              have h1 := hCf (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
              have h2 : ‖V.mult x - V.mult z‖ = ‖V.mult z - V.mult x‖ := norm_sub_rev _ _
              rw [h2]
              exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            · rw [indicator_of_notMem hz, mul_zero]
              have : Poincare.SimonGMT.Chapter03.blowUpMap x r z ∉
                  closedBall (0 : Amb n ℓ) A₀ := by
                rwa [hmemb x hr]
              simp [hfA _ this]
        have hint : ∫ z, Cf * B.indicator (fun z => ‖V.mult z - V.mult x‖) z ∂ν =
            Cf * (ν.real B * ⨍ z in B, ‖V.mult z - V.mult x‖ ∂ν) := by
          rw [integral_const_mul, integral_indicator measurableSet_closedBall,
            ← measure_smul_setAverage _ (measure_ne_top ν B), smul_eq_mul]
        have havg0 : 0 ≤ ⨍ z in B, ‖V.mult z - V.mult x‖ ∂ν := by
          rw [setAverage_eq, smul_eq_mul]
          exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
            (integral_nonneg fun z => norm_nonneg _)
        have hpow : r⁻¹ ^ n = A₀ ^ n * (r * A₀)⁻¹ ^ n := by
          rw [mul_inv, mul_pow, mul_left_comm, ← mul_pow A₀, mul_inv_cancel₀ hA₀pos.ne', one_pow,
            mul_one]
        rw [heq, norm_mul, Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr hr).le n)]
        calc r⁻¹ ^ n *
              ‖∫ z, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * (V.mult x - V.mult z) ∂ν‖
            ≤ r⁻¹ ^ n * (Cf * (ν.real B * ⨍ z in B, ‖V.mult z - V.mult x‖ ∂ν)) := by
              rw [← hint]
              exact mul_le_mul_of_nonneg_left hbound (pow_nonneg (inv_pos.mpr hr).le n)
          _ = Cf * A₀ ^ n * ((r * A₀)⁻¹ ^ n * ν.real B) * ⨍ z in B, ‖V.mult z - V.mult x‖ ∂ν := by
              rw [hpow]; ring
          _ ≤ Cf * A₀ ^ n * C * ⨍ z in B, ‖V.mult z - V.mult x‖ ∂ν := by
              apply mul_le_mul_of_nonneg_right _ havg0
              exact mul_le_mul_of_nonneg_left hrC (mul_nonneg hCf0 (pow_nonneg hA₀pos.le n))
      · simpa using havg.const_mul (Cf * A₀ ^ n * C)
    have hUnlim : Tendsto (fun r => V.mult x * Un r) (𝓝[>] 0) (𝓝 (V.mult x * L)) := by
      have := hdiff.add hWtlim
      simpa using this
    have := hUnlim.const_mul (V.mult x)⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ ha.ne'] using this
  -- the tangent field
  classical
  let T' : Amb n ℓ → Submodule ℝ (Amb n ℓ) := fun x =>
    if h : ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P
    then Classical.choose h else ⊥
  have hT' : ∀ x, (T' x).starProjection = V.tangentProj x := by
    intro x
    by_cases h : ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P
    · simp only [T', RectifiableVarifold.tangentProj, h, ↓reduceDIte]
    · simp only [T', RectifiableVarifold.tangentProj, h, ↓reduceDIte, Submodule.starProjection_bot]
  have happrox : ∀ᵐ x ∂ν,
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n M' x (T' x) := by
    have hνμ : ν ≪ μ := Measure.absolutelyContinuous_of_le (hνle.trans Measure.restrict_le_self)
    filter_upwards [hbr, hνμ.ae_le htan, ae_restrict_mem hM'meas] with x hx hxt hxM'
    obtain ⟨P, -, hP, -⟩ := hxt
    have hex : ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P :=
      ⟨P, hP⟩
    have hTx : T' x = P := by
      simp only [T', hex, ↓reduceDIte]
      exact (Classical.choose_spec hex).unique (V.mult_pos x (hM'M hxM')).ne' hP
    rw [hTx]
    exact hx P hP
  -- the Chapter 4 varifold
  have hw' : (μHE[n] : Measure (Amb n ℓ)).withDensity
      (M'.indicator fun x => ENNReal.ofReal (V.mult x)) = μ.restrict W := by
    rw [withDensity_indicator hM'meas, hμW_eq]
  have hfinW : IsFiniteMeasure (μ.restrict W) := isFiniteMeasure_restrict.mpr hμW.ne
  let V' : Poincare.SimonGMT.Chapter04.RectifiableVarifold (E := Amb n ℓ) n :=
    { carrier := M'
      measurable_carrier := hM'meas
      rectifiable_carrier := V.countablyRectifiable.mono hM'M
      multiplicity := V.mult
      multiplicity_hypotheses := ⟨hM'meas, fun x hx => V.mult_pos x (hM'M hx),
        V.aemeasurable_mult.mono_measure (Measure.restrict_mono hM'M le_rfl),
        fun K _ => hθint.mono_set inter_subset_left⟩
      tangent := T'
      approximate_tangent := happrox
      tangentProjection_aemeasurable := by
        rw [hw', funext hT']
        exact htanm.aemeasurable.mono_measure Measure.restrict_le_self
      locallyFiniteWeight := by
        rw [hw']
        infer_instance }
  have hV'w : V'.weight = μ.restrict W := hw'
  have hV'tan : ∀ x, V'.tangentProjection x = V.tangentProj x := hT'
  -- generalized mean curvature of `V'` in `W`
  have hH' : V'.HasGeneralizedMeanCurvatureIn W H := by
    constructor
    · rw [hV'w]
      intro x hx
      obtain ⟨s, hs, hint⟩ := hH.1 x (hWU hx)
      exact ⟨s, nhdsWithin_mono x hWU hs, hint.mono_measure Measure.restrict_le_self⟩
    · intro X hX
      obtain ⟨hXc, hXcs, hXsupp⟩ := hX
      have hdiv : ∀ x, V'.tangentialDivergence X x = V.divM X x := by
        intro x
        simp only [Poincare.SimonGMT.Chapter04.RectifiableVarifold.tangentialDivergence,
          hV'tan, RectifiableVarifold.divM]
      have hzero : ∀ x, x ∉ W → V.divM X x = 0 := by
        intro x hx
        have hx' : x ∉ tsupport X := fun h => hx (hXsupp h)
        have hfd : fderiv ℝ X x = 0 := by
          by_contra hne
          exact hx' (support_fderiv_subset ℝ hne)
        simp [RectifiableVarifold.divM, hfd]
      have hzero' : ∀ x, x ∉ W → inner ℝ (X x) (H x) = 0 := by
        intro x hx
        have hx' : x ∉ tsupport X := fun h => hx (hXsupp h)
        rw [image_eq_zero_of_notMem_tsupport hx', inner_zero_left]
      show ∫ x, V'.tangentialDivergence X x ∂V'.weight =
        -∫ x, inner ℝ (X x) (H x) ∂V'.weight
      simp_rw [hdiv]
      rw [hV'w, setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
        setIntegral_eq_integral_of_forall_compl_eq_zero hzero']
      exact hH.2 X hXc hXcs (hXsupp.trans hWU)
  -- `Lᵖ` facts
  have hI : ∫⁻ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ₑ ^ p ∂μ < ∞ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    have h1 := hLpscale
    simp only [RectifiableVarifold.scaledLpNorm] at h1
    rw [hcon, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ _)).ne',
      ENNReal.top_rpow_of_pos (one_div_pos.mpr hp0)] at h1
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h1)
  have hHae : AEStronglyMeasurable H (μ.restrict (closedBall (0 : Amb n ℓ) ρ)) :=
    (hH.1.integrableOn_compact_subset hballU (isCompact_closedBall 0 ρ)).aestronglyMeasurable
  have hMemLp : MemLp H (ENNReal.ofReal p) (μ.restrict (closedBall (0 : Amb n ℓ) ρ)) := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top hHae, ENNReal.toReal_ofReal hp0.le]
    exact hI
  have hLpW : MemLp H (ENNReal.ofReal p) (V'.weight.restrict W) := by
    rw [hV'w]
    exact hMemLp.mono_measure (Measure.restrict_mono hWcb Measure.restrict_le_self)
  have hLpK : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ W →
      MemLp H (ENNReal.ofReal p) (V'.weight.restrict K) := by
    intro K _ hKW
    rw [hV'w]
    exact hMemLp.mono_measure (Measure.restrict_mono (hKW.trans hWcb) Measure.restrict_le_self)
  have hθ' : ∀ᵐ x ∂V'.weight.restrict W, 1 ≤ V'.multiplicity x := by
    rw [hV'w]
    exact ae_restrict_of_ae (ae_restrict_of_ae hθ1)
  have hJ : (∫ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ ^ p ∂μ) =
      (∫⁻ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ₑ ^ p ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity)
      (hHae.norm.aemeasurable.pow_const p).aestronglyMeasurable]
    congr 1
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm]
  have hscaleρ : (ρ ^ (p - n) * ∫ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ ^ p ∂μ) ^ (1 / p) ≤ δ := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hLpscale
    simp only [RectifiableVarifold.scaledLpNorm] at h1
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hρ.le _),
      ENNReal.toReal_ofReal hδ.le] at h1
    rw [hJ]
    exact h1
  have hscale : ∀ (y : Amb n ℓ) (R : ℝ), 0 < R → R ≤ ρ → closedBall y R ⊆ W →
      V'.scaledLpMeanCurvature y H p R ≤
        Poincare.SimonGMT.Chapter04.RectifiableVarifold.lpMeanCurvatureKappa n p * Λ := by
    intro y R hR hRρ hsub
    rw [hκΛ]
    refine le_trans ?_ hscaleρ
    simp only [Poincare.SimonGMT.Chapter04.RectifiableVarifold.scaledLpMeanCurvature]
    rw [hV'w, Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.mpr hsub]
    have hint : IntegrableOn (fun x => ‖H x‖ ^ p) (closedBall (0 : Amb n ℓ) ρ) μ := by
      have := hMemLp.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      simp only [ENNReal.toReal_ofReal hp0.le] at this
      exact this
    have hle : (∫ x in closedBall y R, ‖H x‖ ^ p ∂μ) ≤
        ∫ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ ^ p ∂μ :=
      setIntegral_mono_set hint (Eventually.of_forall fun x => by positivity)
        (Eventually.of_forall (hsub.trans hWcb))
    apply Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hR.le _)
      (integral_nonneg fun x => by positivity)) _ (one_div_pos.mpr hp0).le
    exact mul_le_mul (Real.rpow_le_rpow hR.le hRρ hpn.le) hle
      (integral_nonneg fun x => by positivity) (Real.rpow_nonneg hρ.le _)
  -- the annular correction
  have hann : ∀ (y : Amb n ℓ) (R : ℝ), 0 < R → R ≤ ρ → closedBall y R ⊆ W →
      ∃ F G, V'.LpAnnularCorrection y p R Λ F G := fun y R hR hRρ hsub =>
    hH'.exists_lpAnnularCorrection_of_memLp _ hWo y hp hR hsub hLpW (hscale y R hR hRρ hsub)
  have hFb : ∀ (y : Amb n ℓ) (R : ℝ) (F : ℝ → ℝ) (G : ℝ → ℝ → ℝ), 0 < R →
      V'.LpAnnularCorrection y p R Λ F G → ∀ t, 0 < t → t ≤ R →
      Real.exp (-Λ) ≤ F t ∧ F t ≤ Real.exp Λ ∧ |F t - 1| ≤ Λ := by
    intro y R F G hR hc t ht htR
    have h1 := hc.factor_bounds t ⟨ht, htR⟩
    have h2 := hc.error_bound_of_le_one hΛ1 t ⟨ht, htR⟩
    have hα : 0 ≤ 1 - (n : ℝ) / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
    have hpow : (t / R) ^ (1 - (n : ℝ) / p) ≤ 1 :=
      Real.rpow_le_one (div_pos ht hR).le ((div_le_one hR).mpr htR) hα
    refine ⟨h1.1.trans h1.2.1, h1.2.2.1.trans h1.2.2.2, h2.trans ?_⟩
    calc Λ * (t / R) ^ (1 - (n : ℝ) / p) ≤ Λ * 1 := mul_le_mul_of_nonneg_left hpow hΛpos.le
      _ = Λ := mul_one Λ
  have hF1 : ∀ (y : Amb n ℓ) (R : ℝ) (F : ℝ → ℝ) (G : ℝ → ℝ → ℝ), 0 < R →
      V'.LpAnnularCorrection y p R Λ F G → Tendsto F (𝓝[>] 0) (𝓝 1) := by
    intro y R F G hR hc
    have hα : 0 < 1 - (n : ℝ) / p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
    have hlim : Tendsto (fun t : ℝ => Λ * (t / R) ^ (1 - (n : ℝ) / p)) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => t / R) (𝓝[>] 0) (𝓝 0) := by
        simpa using (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).div_const R
      have h2 := (Real.continuousAt_rpow_const 0 (1 - (n : ℝ) / p) (Or.inr hα.le)).tendsto.comp h1
      rw [Real.zero_rpow hα.ne'] at h2
      simpa using h2.const_mul Λ
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioc_mem_nhdsGT hR] with t ht
    rw [norm_norm, Real.norm_eq_abs]
    exact hc.error_bound_of_le_one hΛ1 t ht
  -- densities
  have hdens : ∀ y ∈ W, Tendsto (fun t => V'.weight.real (closedBall y t) / t ^ n) (𝓝[>] 0)
      (𝓝 (ω * V'.stationaryDensityReal y)) := by
    intro y hy
    have h := hH'.tendsto_densityQuotient_real_lp _ hp hWo hLpK hy
    rw [hω'] at h
    refine (h.const_mul ω).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    field_simp
  have hsuppW : ∀ y ∈ W, y ∈ μ.support → y ∈ V'.weight.support := by
    intro y hyW hy
    rw [hV'w, Measure.mem_support_iff_forall]
    intro N hN
    have h1 := (Measure.mem_support_iff_forall y).mp hy (N ∩ W) (inter_mem hN (hWo.mem_nhds hyW))
    exact h1.trans_le (Measure.le_restrict_apply _ _)
  have hPhi : ∀ y ∈ W, y ∈ μ.support → ∀ (R : ℝ) (F : ℝ → ℝ) (G : ℝ → ℝ → ℝ), 0 < R →
      V'.LpAnnularCorrection y p R Λ F G → ∀ s, 0 < s → s ≤ R →
      ω ≤ F s * (V'.weight.real (closedBall y s) / s ^ n) + (F s - 1) := by
    intro y hyW hy R F G hR hc s hs hsR
    have hd1 : 1 ≤ V'.stationaryDensityReal y :=
      hH'.one_le_stationaryDensityReal_of_mem_support_lp hWo (by omega) hp hLpK hθ' hyW
        (hsuppW y hyW hy)
    have hlim : Tendsto (fun t => F t * (V'.weight.real (closedBall y t) / t ^ n) + (F t - 1))
        (𝓝[>] 0) (𝓝 (1 * (ω * V'.stationaryDensityReal y) + (1 - 1))) :=
      ((hF1 y R F G hR hc).mul (hdens y hyW)).add ((hF1 y R F G hR hc).sub_const 1)
    rw [one_mul, sub_self, add_zero] at hlim
    have hle : ω * V'.stationaryDensityReal y ≤
        F s * (V'.weight.real (closedBall y s) / s ^ n) + (F s - 1) := by
      apply le_of_tendsto hlim
      filter_upwards [Ioc_mem_nhdsGT hs] with t ht
      exact hc.monotone ⟨ht.1, ht.2.trans hsR⟩ ⟨hs, hsR⟩ ht.2
    calc ω = ω * 1 := (mul_one ω).symm
      _ ≤ ω * V'.stationaryDensityReal y := mul_le_mul_of_nonneg_left hd1 hωpos.le
      _ ≤ _ := hle
  -- ball geometry
  have hnorm_le : ∀ (y : Amb n ℓ) (R : ℝ), 0 ≤ R →
      closedBall y R ⊆ closedBall (0 : Amb n ℓ) ρ → ‖y‖ + R ≤ ρ := by
    intro y R hR hsub
    by_cases hy : y = 0
    · subst hy
      have : Nonempty (Fin (n + ℓ)) := ⟨⟨0, by omega⟩⟩
      obtain ⟨z, hz⟩ := exists_norm_eq (Amb n ℓ) hR
      have hz' : z ∈ closedBall (0 : Amb n ℓ) R := by
        rw [mem_closedBall, dist_zero_right, hz]
      have := hsub hz'
      rw [mem_closedBall, dist_zero_right, hz] at this
      simpa using this
    · have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hz : y + (R / ‖y‖) • y ∈ closedBall y R := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg (div_nonneg hR hy0.le), div_mul_cancel₀ R hy0.ne']
      have h1 := hsub hz
      rw [mem_closedBall, dist_zero_right] at h1
      have hzn : ‖y + (R / ‖y‖) • y‖ = ‖y‖ + R := by
        have : y + (R / ‖y‖) • y = (1 + R / ‖y‖) • y := by rw [add_smul, one_smul]
        rw [this, norm_smul, Real.norm_of_nonneg (by positivity)]
        field_simp
      linarith
  have hball_W : ∀ (y : Amb n ℓ) (R R' : ℝ), 0 ≤ R → R' < R →
      closedBall y R ⊆ closedBall (0 : Amb n ℓ) ρ → closedBall y R' ⊆ W := by
    intro y R R' hR hR'R hsub z hz
    have h1 := hnorm_le y R hR hsub
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [hWdef, mem_ball, dist_zero_right]
    calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
      _ < ‖y‖ + R := by linarith
      _ ≤ ρ := h1
  have hreal : ∀ (y : Amb n ℓ) (t : ℝ), closedBall y t ⊆ W →
      V'.weight.real (closedBall y t) = (μ (closedBall y t)).toReal := by
    intro y t hsub
    rw [measureReal_def, hV'w, Measure.restrict_apply measurableSet_closedBall,
      inter_eq_left.mpr hsub]
  refine ⟨?_, ?_, ?_⟩
  · -- (M1)
    intro y R s r hs hsr hrR hsub
    have hR0 : 0 ≤ R := by linarith
    have hyR := hnorm_le y R hR0 hsub
    have hR''pos : 0 < (r + R) / 2 := by linarith
    have hrR'' : r ≤ (r + R) / 2 := by linarith
    have hR''R : (r + R) / 2 < R := by linarith
    have hR''ρ : (r + R) / 2 ≤ ρ := by linarith [norm_nonneg y]
    have hsubW := hball_W y R ((r + R) / 2) hR0 hR''R hsub
    obtain ⟨F, G, hc⟩ := hann y ((r + R) / 2) hR''pos hR''ρ hsubW
    have hr : 0 < r := hs.trans_le hsr
    have hFs := hFb y _ F G hR''pos hc s hs (hsr.trans hrR'')
    have hFr := hFb y _ F G hR''pos hc r hr hrR''
    have hmono := hc.monotone ⟨hs, hsr.trans hrR''⟩ ⟨hr, hrR''⟩ hsr
    simp only at hmono
    rw [hreal y s ((closedBall_subset_closedBall (hsr.trans hrR'')).trans hsubW),
      hreal y r ((closedBall_subset_closedBall hrR'').trans hsubW)] at hmono
    set ms := (μ (closedBall y s)).toReal / s ^ n with hmsdef
    set mr := (μ (closedBall y r)).toReal / r ^ n with hmrdef
    have hms : 0 ≤ ms := div_nonneg ENNReal.toReal_nonneg (pow_nonneg hs.le n)
    have hmr : 0 ≤ mr := div_nonneg ENNReal.toReal_nonneg (pow_nonneg hr.le n)
    have hexp : Real.exp (2 * Λ) = Real.exp Λ * Real.exp Λ := by rw [two_mul, Real.exp_add]
    have hexpinv : Real.exp Λ * Real.exp (-Λ) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h1 : F s * ms ≤ Real.exp Λ * mr + 2 * Λ := by
      have h3 := abs_le.mp hFs.2.2
      have h4 := abs_le.mp hFr.2.2
      have h5 := mul_le_mul_of_nonneg_right hFr.2.1 hmr
      linarith
    have h2 : ms ≤ Real.exp Λ * (F s * ms) := by
      calc ms = Real.exp Λ * (Real.exp (-Λ) * ms) := by rw [← mul_assoc, hexpinv, one_mul]
        _ ≤ Real.exp Λ * (F s * ms) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hFs.1 hms) (Real.exp_pos _).le
    rw [hexp]
    calc ms ≤ Real.exp Λ * (F s * ms) := h2
      _ ≤ Real.exp Λ * (Real.exp Λ * mr + 2 * Λ) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp Λ * Real.exp Λ * mr + 2 * Real.exp Λ * Λ := by ring
  · -- (M2)
    intro y hy R s hs hsR hsub
    have hR0 : 0 ≤ R := by linarith
    have hyR := hnorm_le y R hR0 hsub
    have hyW : y ∈ W := by
      rw [hWdef, mem_ball, dist_zero_right]
      linarith
    have hR''pos : 0 < (s + R) / 2 := by linarith
    have hsR'' : s ≤ (s + R) / 2 := by linarith
    have hR''R : (s + R) / 2 < R := by linarith
    have hR''ρ : (s + R) / 2 ≤ ρ := by linarith [norm_nonneg y]
    have hsubW := hball_W y R ((s + R) / 2) hR0 hR''R hsub
    obtain ⟨F, G, hc⟩ := hann y ((s + R) / 2) hR''pos hR''ρ hsubW
    have hlow := hPhi y hyW hy.2 _ F G hR''pos hc s hs hsR''
    have hFs := hFb y _ F G hR''pos hc s hs hsR''
    rw [hreal y s ((closedBall_subset_closedBall hsR'').trans hsubW)] at hlow
    set ms := (μ (closedBall y s)).toReal / s ^ n with hmsdef
    have hms : 0 ≤ ms := div_nonneg ENNReal.toReal_nonneg (pow_nonneg hs.le n)
    have hsn : 0 < s ^ n := pow_pos hs n
    have hμs : (μ (closedBall y s)).toReal = ms * s ^ n := by
      rw [hmsdef, div_mul_cancel₀ _ hsn.ne']
    rw [hμs]
    have h1 : ω - Λ ≤ F s * ms := by
      have := abs_le.mp hFs.2.2
      linarith
    have h2 : Real.exp (-Λ) * F s ≤ 1 := by
      calc Real.exp (-Λ) * F s ≤ Real.exp (-Λ) * Real.exp Λ :=
            mul_le_mul_of_nonneg_left hFs.2.1 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h3 : Real.exp (-Λ) * (ω - Λ) ≤ ms := by
      calc Real.exp (-Λ) * (ω - Λ) ≤ Real.exp (-Λ) * (F s * ms) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = (Real.exp (-Λ) * F s) * ms := by ring
        _ ≤ 1 * ms := mul_le_mul_of_nonneg_right h2 hms
        _ = ms := one_mul _
    exact mul_le_mul_of_nonneg_right h3 hsn.le
  · -- (M3)
    have h0W : (0 : Amb n ℓ) ∈ W := mem_ball_self hρ
    have h0supp' : (0 : Amb n ℓ) ∈ μ.support := h0supp.2
    set g : Amb n ℓ → ℝ≥0∞ := fun x =>
      ENNReal.ofReal (‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2)) with hgdef
    set B : ℝ → ℝ := fun r =>
      Real.exp Λ * (Real.exp Λ * (1 + δ) * ω * (ρ / r) ^ n + Λ - ω) with hBdef
    have hμρreal : (μ (closedBall (0 : Amb n ℓ) ρ)).toReal ≤ (1 + δ) * (ω * ρ ^ n) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hmass
    have hstep : ∀ t r : ℝ, 0 < t → t ≤ r → r < ρ →
        ∫⁻ x in closedBall (0 : Amb n ℓ) r \ closedBall 0 t, g x ∂μ ≤ ENNReal.ofReal (B r) := by
      intro t r ht htr hrρ
      have hr : 0 < r := ht.trans_le htr
      have hR''pos : 0 < (r + ρ) / 2 := by linarith
      have hrR'' : r ≤ (r + ρ) / 2 := by linarith
      have hR''ρ : (r + ρ) / 2 < ρ := by linarith
      have hsubW : closedBall (0 : Amb n ℓ) ((r + ρ) / 2) ⊆ W := closedBall_subset_ball hR''ρ
      obtain ⟨F, G, hc⟩ := hann 0 _ hR''pos hR''ρ.le hsubW
      set A := closedBall (0 : Amb n ℓ) r \ closedBall 0 t with hA
      have hAW : A ⊆ W := sdiff_subset.trans ((closedBall_subset_closedBall hrR'').trans hsubW)
      have hAmeas : MeasurableSet A := measurableSet_closedBall.diff measurableSet_closedBall
      have hid := hc.annular_identity t r ht htr hrR''
      have hG := hc.annular_factor_bounds t r ht htr hrR''
      set D := ∫ x in A, V'.radialNormalSq 0 x / ‖x - 0‖ ^ n ∂V'.weight with hD
      have hD0 : 0 ≤ D := integral_nonneg fun x =>
        div_nonneg (V'.radialNormalSq_nonneg 0 x) (pow_nonneg (norm_nonneg _) n)
      have hAt : ∀ x ∈ A, t < ‖x‖ := by
        intro x hx
        have := hx.2
        rwa [mem_closedBall, dist_zero_right, not_le] at this
      have hint : IntegrableOn (fun x => V'.radialNormalSq 0 x / ‖x - 0‖ ^ n) A V'.weight := by
        have hfin' : V'.weight A ≠ ∞ := by
          rw [hV'w]
          exact measure_ne_top _ _
        refine Measure.integrableOn_of_bounded (M := (t ^ n)⁻¹) hfin' ?_ ?_
        · exact ((V'.radialNormalSq_aemeasurable 0).div
            ((continuous_norm.comp (continuous_id.sub continuous_const)).pow n).aemeasurable
            ).aestronglyMeasurable
        · filter_upwards [ae_restrict_mem hAmeas] with x hx
          have hxt := hAt x hx
          have htn : 0 < t ^ n := pow_pos ht n
          have hxn : t ^ n ≤ ‖x - 0‖ ^ n := by
            rw [sub_zero]
            exact pow_le_pow_left₀ ht.le hxt.le n
          rw [Real.norm_of_nonneg (div_nonneg (V'.radialNormalSq_nonneg 0 x)
            (pow_nonneg (norm_nonneg _) n))]
          calc V'.radialNormalSq 0 x / ‖x - 0‖ ^ n ≤ 1 / ‖x - 0‖ ^ n :=
                div_le_div_of_nonneg_right (V'.radialNormalSq_le_one 0 x)
                  (pow_nonneg (norm_nonneg _) n)
            _ ≤ 1 / t ^ n := one_div_le_one_div_of_le htn hxn
            _ = (t ^ n)⁻¹ := one_div _
      have hpt : ∀ x ∈ A, ENNReal.ofReal (V'.radialNormalSq 0 x / ‖x - 0‖ ^ n) = g x := by
        intro x hx
        have hxn : 0 < ‖x‖ := ht.trans (hAt x hx)
        have hN : V'.normalProjection x (‖x - 0‖⁻¹ • (x - 0)) =
            ‖x‖⁻¹ • (x - V.tangentProj x x) := by
          simp only [Poincare.SimonGMT.Chapter04.RectifiableVarifold.normalProjection, hV'tan,
            sub_apply, ContinuousLinearMap.id_apply, map_smul, smul_sub,
            sub_zero]
        show ENNReal.ofReal (V'.radialNormalSq 0 x / ‖x - 0‖ ^ n) =
          ENNReal.ofReal (‖x - V.tangentProj x x‖ ^ 2 / ‖x‖ ^ (n + 2))
        rw [V'.radialNormalSq_eq, hN, norm_smul, mul_pow,
          Real.norm_of_nonneg (inv_nonneg.mpr hxn.le), sub_zero, pow_add]
        congr 1
        field_simp
      have hlin : ∫⁻ x in A, g x ∂μ = ENNReal.ofReal D := by
        rw [hD, ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun x => div_nonneg (V'.radialNormalSq_nonneg 0 x)
            (pow_nonneg (norm_nonneg _) n)),
          hV'w, Measure.restrict_restrict hAmeas, inter_eq_left.mpr hAW]
        exact (setLIntegral_congr_fun hAmeas hpt).symm
      -- bound on `D`
      have hPt := hPhi 0 h0W h0supp' _ F G hR''pos hc t ht (htr.trans hrR'')
      have hFr := hFb 0 _ F G hR''pos hc r hr hrR''
      rw [hreal 0 r ((closedBall_subset_closedBall hrR'').trans hsubW)] at hid
      set mr := (μ (closedBall (0 : Amb n ℓ) r)).toReal / r ^ n with hmrdef
      have hmr0 : 0 ≤ mr := div_nonneg ENNReal.toReal_nonneg (pow_nonneg hr.le n)
      have hmrle : mr ≤ (1 + δ) * ω * (ρ / r) ^ n := by
        have h1 : (μ (closedBall (0 : Amb n ℓ) r)).toReal ≤ (1 + δ) * (ω * ρ ^ n) :=
          (ENNReal.toReal_mono hμρ.ne (measure_mono (closedBall_subset_closedBall hrρ.le))).trans
            hμρreal
        rw [hmrdef, div_pow, div_le_iff₀ (pow_pos hr n)]
        calc (μ (closedBall (0 : Amb n ℓ) r)).toReal ≤ (1 + δ) * (ω * ρ ^ n) := h1
          _ = (1 + δ) * ω * (ρ ^ n / r ^ n) * r ^ n := by
              field_simp
      have hPr : F r * mr + (F r - 1) ≤ Real.exp Λ * ((1 + δ) * ω * (ρ / r) ^ n) + Λ := by
        have h3 := abs_le.mp hFr.2.2
        have h4 : F r * mr ≤ Real.exp Λ * mr := mul_le_mul_of_nonneg_right hFr.2.1 hmr0
        have h5 : Real.exp Λ * mr ≤ Real.exp Λ * ((1 + δ) * ω * (ρ / r) ^ n) :=
          mul_le_mul_of_nonneg_left hmrle (Real.exp_pos _).le
        linarith
      have hGD : Real.exp (-Λ) * D ≤ G t r * D := mul_le_mul_of_nonneg_right hG.1 hD0
      have hDle : D ≤ Real.exp Λ * (G t r * D) := by
        calc D = Real.exp Λ * (Real.exp (-Λ) * D) := by
              rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
          _ ≤ Real.exp Λ * (G t r * D) := mul_le_mul_of_nonneg_left hGD (Real.exp_pos _).le
      have hDB : D ≤ B r := by
        rw [← hid] at hDle
        have hexp0 := Real.exp_pos Λ
        have h6 : F r * mr + (F r - 1) -
            (F t * (V'.weight.real (closedBall 0 t) / t ^ n) + (F t - 1)) ≤
            Real.exp Λ * ((1 + δ) * ω * (ρ / r) ^ n) + Λ - ω := by linarith
        calc D ≤ Real.exp Λ * (F r * mr + (F r - 1) -
              (F t * (V'.weight.real (closedBall 0 t) / t ^ n) + (F t - 1))) := hDle
          _ ≤ Real.exp Λ * (Real.exp Λ * ((1 + δ) * ω * (ρ / r) ^ n) + Λ - ω) :=
              mul_le_mul_of_nonneg_left h6 hexp0.le
          _ = B r := by rw [hBdef]; ring
      rw [hlin]
      exact ENNReal.ofReal_le_ofReal hDB
    -- the limit
    set tk : ℕ → ℝ := fun k => ρ / ((k : ℝ) + 2) with htkdef
    set rk : ℕ → ℝ := fun k => ρ - ρ / ((k : ℝ) + 2) with hrkdef
    have htkpos : ∀ k, 0 < tk k := fun k => div_pos hρ (by positivity)
    have htkr : ∀ k, tk k ≤ rk k := by
      intro k
      simp only [htkdef, hrkdef]
      have h2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have : ρ / ((k : ℝ) + 2) ≤ ρ / 2 := div_le_div_of_nonneg_left hρ.le (by norm_num) h2
      linarith
    have hrkρ : ∀ k, rk k < ρ := fun k => sub_lt_self ρ (htkpos k)
    have htk_anti : Antitone tk := by
      intro i j hij
      simp only [htkdef]
      apply div_le_div_of_nonneg_left hρ.le (by positivity)
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith
    have hrk_mono : Monotone rk := fun i j hij => by
      simp only [hrkdef]
      linarith [htk_anti hij]
    set Ak : ℕ → Set (Amb n ℓ) := fun k =>
      closedBall (0 : Amb n ℓ) (rk k) \ closedBall 0 (tk k) with hAkdef
    have hAmono : Monotone Ak := by
      intro i j hij x hx
      exact ⟨closedBall_subset_closedBall (hrk_mono hij) hx.1,
        fun h => hx.2 (closedBall_subset_closedBall (htk_anti hij) h)⟩
    have hAkmeas : ∀ k, MeasurableSet (Ak k) := fun k =>
      measurableSet_closedBall.diff measurableSet_closedBall
    have hcover : ball (0 : Amb n ℓ) ρ ⊆ (⋃ k, Ak k) ∪ {0} := by
      intro x hx
      by_cases hx0 : x = 0
      · exact Or.inr hx0
      · left
        rw [mem_ball, dist_zero_right] at hx
        have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        have hm : 0 < min ‖x‖ (ρ - ‖x‖) := lt_min hxpos (by linarith)
        obtain ⟨k, hk⟩ := exists_nat_gt (ρ / min ‖x‖ (ρ - ‖x‖))
        have hk2 : ρ / min ‖x‖ (ρ - ‖x‖) < (k : ℝ) + 2 := by linarith
        have htk : tk k < min ‖x‖ (ρ - ‖x‖) := by
          simp only [htkdef]
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hm] at hk2
          linarith
        refine mem_iUnion.mpr ⟨k, ?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right]
          simp only [hrkdef]
          have := htk.trans_le (min_le_right _ _)
          simp only [htkdef] at this
          linarith
        · rw [mem_closedBall, dist_zero_right, not_le]
          exact htk.trans_le (min_le_left _ _)
    have hBlim : Tendsto (fun k => ENNReal.ofReal (B (rk k))) atTop
        (𝓝 (ENNReal.ofReal (B ρ))) := by
      apply (ENNReal.continuous_ofReal.tendsto _).comp
      have hg2 : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have hrklim : Tendsto rk atTop (𝓝 ρ) := by
        have h1 : Tendsto (fun k : ℕ => ρ / ((k : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop hg2
        simpa [hrkdef] using (tendsto_const_nhds (x := ρ)).sub h1
      have hBc : ContinuousAt B ρ := by
        simp only [hBdef]
        fun_prop (disch := exact hρ.ne')
      exact hBc.tendsto.comp hrklim
    have hbound_k : ∀ k, ∫⁻ x in Ak k, g x ∂μ ≤ ENNReal.ofReal (B ρ) := by
      intro k
      apply ge_of_tendsto hBlim
      filter_upwards [eventually_ge_atTop k] with j hj
      calc ∫⁻ x in Ak k, g x ∂μ ≤ ∫⁻ x in Ak j, g x ∂μ := lintegral_mono_set (hAmono hj)
        _ ≤ ENNReal.ofReal (B (rk j)) := hstep (tk j) (rk j) (htkpos j) (htkr j) (hrkρ j)
    have hg0 : g 0 = 0 := by simp [hgdef]
    have hiU : ∫⁻ x in ⋃ k, Ak k, g x ∂μ = ⨆ k, ∫⁻ x in Ak k, g x ∂μ := by
      rw [← withDensity_apply _ (MeasurableSet.iUnion hAkmeas), hAmono.measure_iUnion]
      congr 1
      funext k
      rw [withDensity_apply _ (hAkmeas k)]
    have hBρ : B ρ = Real.exp Λ * (Real.exp Λ * (1 + δ) * ω + Λ - ω) := by
      simp only [hBdef, div_self hρ.ne', one_pow, mul_one]
    calc ∫⁻ x in ball (0 : Amb n ℓ) ρ, g x ∂μ
        ≤ ∫⁻ x in (⋃ k, Ak k) ∪ {0}, g x ∂μ := lintegral_mono_set hcover
      _ ≤ ∫⁻ x in ⋃ k, Ak k, g x ∂μ + ∫⁻ x in ({0} : Set (Amb n ℓ)), g x ∂μ :=
          lintegral_union_le _ _ _
      _ = ⨆ k, ∫⁻ x in Ak k, g x ∂μ := by rw [lintegral_singleton, hg0, zero_mul, add_zero, hiU]
      _ ≤ ENNReal.ofReal (B ρ) := iSup_le hbound_k
      _ = ENNReal.ofReal (Real.exp Λ * (Real.exp Λ * (1 + δ) * ω + Λ - ω)) := by rw [hBρ]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
