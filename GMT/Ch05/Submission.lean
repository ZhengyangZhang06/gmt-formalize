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
import Poincare.SimonGMT.Chapter04.LpMeanCurvature
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

open Poincare.SimonGMT.Chapter04.RectifiableVarifold in
set_option maxHeartbeats 800000 in
/-- **Density bounds and annular monotonicity under 2.3** (Simon Ch. 5, 2.4 and 2.6 (9); the
monotonicity identity of Ch. 4, §§3–4 with the plus sign of the mean-curvature term forced by the
contract's convention `∫ div_M X = -∫ X·H`, and `κ = (p - n)/(4p)`).  For `n ≥ 1` and `p > n` there
are `δ₀ ∈ (0, 1/8]` and `C₀ ≥ 0` such that, under 2.3 with `δ ≤ δ₀`, for `|y| ≤ 3δρ` and
`0 < s ≤ r ≤ ρ/2`: (i) `μ_V(B_s(y)) ≤ 2 ωₙ sⁿ`; (ii) `μ_V(B_s(y)) ≥ ωₙ sⁿ / 2` if `y ∈ spt V`;
(iii) `r⁻ⁿ μ_V(B_r(y)) ≤ e² s⁻ⁿ μ_V(B_s(y)) + C₀ δ +
e² ∫_{B_r(y) \ B_s(y)} |p_x^⊥(x-y)|²/|x-y|^{n+2}`.

Proof.  `lgc_tangent_plane_ae` makes `p_x` a rank-`n` orthogonal projection `μ_V`-a.e., so the first
variation of `X = η(|x-y|²)(x-y)` gives the radial identity.  For the cutoffs
`φ_ε(|x-y|²/t²)` the scale derivative of `t⁻ⁿ I_ε(t)` is the normal-radial term plus the curvature
term `E_ε`, and Hölder gives `|E_ε| ≤ 2κΛR⁻¹(t/R)^{-n/p}(1 + t⁻ⁿI_ε)` with `Λ = δ/κ`.  The
explicit factors `F^± = exp(±Λ/2 (t/R)^{1-n/p})` then make `F⁺(1 + t⁻ⁿI_ε)` nondecreasing and
bound the increase of `F⁻(1 + t⁻ⁿI_ε)` by the defect integral; `ε ↓ 0` gives the closed-ball
inequalities.  (i), (iii) follow with `δ₀ = min{1/(64n), κ/16, κωₙ/(4(1+ωₙ))}`, `C₀ = 2/κ`; for
(ii) the weighted blow-up at good points `z` near `y` gives `ωₙ ≤ θ(z)ωₙ ≤` the monotone bound,
which passes to `y` because `B_{s-η}(z) ⊆ B_s(y)`. -/
theorem lgc_density_monotonicity : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₀ C₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 8 ∧ 0 ≤ C₀ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ → (∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → V.weight (closedBall y s) ≤ ENNReal.ofReal (2 * unitBallVolume n * s ^ n)) ∧ (∀ y ∈ V.support, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → ENNReal.ofReal (unitBallVolume n * s ^ n / 2) ≤ V.weight (closedBall y s)) ∧ (∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s r : ℝ, 0 < s → s ≤ r → r ≤ ρ / 2 → (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal ≤ Real.exp 2 * ((s ^ n)⁻¹ * (V.weight (closedBall y s)).toReal) + C₀ * δ + Real.exp 2 * ∫ x in closedBall y r \ closedBall y s, ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight) := by
  -- Differentiation under the integral sign, finite measure version.
  have dm_hasDerivAt_integral_mul : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) [IsFiniteMeasure μ]
      {F F' : ℝ → Amb n ℓ → ℝ} {a b ρ : ℝ} (hρ : ρ ∈ Ioo a b) {K : Set (Amb n ℓ)} (hK : IsCompact K)
      (hF : ∀ t, Continuous (F t)) (hF' : ∀ t, Continuous (F' t))
      (hjoint : ContinuousOn (fun p : ℝ × Amb n ℓ ↦ F' p.1 p.2) (Icc a b ×ˢ K))
      (hzero' : ∀ t ∈ Icc a b, ∀ x ∉ K, F' t x = 0)
      (hderiv : ∀ t ∈ Icc a b, ∀ x, HasDerivAt (fun s ↦ F s x) (F' t x) t) {q : Amb n ℓ → ℝ} {B : ℝ}
      (hq : AEStronglyMeasurable q μ) (hqb : ∀ x, ‖q x‖ ≤ B) (hFb : ∀ x, ‖F ρ x‖ ≤ 1),
      Integrable (fun x ↦ F' ρ x * q x) μ ∧ HasDerivAt (fun t ↦ ∫ x, F t x * q x ∂μ)
        (∫ x, F' ρ x * q x ∂μ) ρ := by
    intro n ℓ μ _ F F' a b ρ hρ K hK hF hF' hjoint hzero' hderiv q B hq hqb hFb
    classical
    have hFint : Integrable (fun x ↦ F ρ x * q x) μ :=
      (integrable_const B).mono' ((hF ρ).aestronglyMeasurable.mul hq) (by
        filter_upwards with x
        rw [norm_mul]
        calc ‖F ρ x‖ * ‖q x‖ ≤ 1 * B :=
              mul_le_mul (hFb x) (hqb x) (norm_nonneg _) zero_le_one
          _ = B := one_mul B)
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hjoint
    let bound : Amb n ℓ → ℝ := K.indicator (fun _ ↦ max C 0 * B)
    have hboundint : Integrable bound μ :=
      (integrableOn_const (measure_lt_top μ K).ne).integrable_indicator hK.measurableSet
    refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t x ↦ F t x * q x) (F' := fun t x ↦ F' t x * q x)
      (Icc_mem_nhds hρ.1 hρ.2)
      (Filter.Eventually.of_forall fun t ↦ (hF t).aestronglyMeasurable.mul hq)
      hFint ((hF' ρ).aestronglyMeasurable.mul hq) ?_ hboundint ?_
    · filter_upwards with x
      intro t ht
      by_cases hx : x ∈ K
      · simp only [bound, indicator_of_mem hx, norm_mul]
        exact mul_le_mul ((hC (t, x) ⟨ht, hx⟩).trans (le_max_left C 0))
          (hqb x) (norm_nonneg _) (le_max_right C 0)
      · simp [bound, hx, hzero' t ht x hx]
    · filter_upwards with x
      intro t ht
      exact (hderiv t ht x).mul_const (q x)

  -- `ε ↓ 0` limit of the cutoff integrals, finite measure version.
  have dm_tendsto_integral_cutoff : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) [IsFiniteMeasure μ]
      (ξ : Amb n ℓ) {ρ : ℝ} (hρ : 0 < ρ) {q : Amb n ℓ → ℝ} {B : ℝ} (hq : AEStronglyMeasurable q μ)
      (hqb : ∀ x, ‖q x‖ ≤ B),
      Tendsto (fun ε ↦ ∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) ρ x * q x ∂μ) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ x in closedBall ξ ρ, q x ∂μ)) := by
    intro n ℓ μ _ ξ ρ hρ q B hq hqb
    classical
    rw [← integral_indicator measurableSet_closedBall]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B) ?_ ?_
      (integrable_const B) ?_
    · exact Filter.Eventually.of_forall fun ε ↦
        (((contDiff_monotonicityCutoff ε).continuous.comp
          (show Continuous (fun x : Amb n ℓ ↦ ‖x - ξ‖ ^ 2 / ρ ^ 2) by
            fun_prop)).aestronglyMeasurable.mul hq)
    · filter_upwards with ε
      filter_upwards with x
      have hcut := monotonicityCutoff_mem_Icc ε (‖x - ξ‖ ^ 2 / ρ ^ 2)
      have hnorm : ‖scaledRadialCutoff ξ (monotonicityCutoff ε) ρ x‖ ≤ 1 := by
        rw [scaledRadialCutoff, Real.norm_eq_abs, abs_of_nonneg hcut.1]
        exact hcut.2
      rw [norm_mul]
      calc ‖scaledRadialCutoff ξ (monotonicityCutoff ε) ρ x‖ * ‖q x‖ ≤ 1 * ‖q x‖ :=
            mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
        _ ≤ B := by simpa using hqb x
    · filter_upwards with x
      convert (tendsto_scaledRadialCutoff ξ x hρ).mul_const (q x) using 1
      by_cases hx : x ∈ closedBall ξ ρ <;> simp [hx]

  -- Hölder with a `[0,1]`-valued cutoff (finite measure).
  have dm_integral_mul_cutoff_le : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) [IsFiniteMeasure μ] {p : ℝ}
      (hp : 1 < p) {f ψ : Amb n ℓ → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ) (hfnonneg : ∀ x, 0 ≤ f x)
      (hψmeas : AEStronglyMeasurable ψ μ) (hψ : ∀ x, ψ x ∈ Icc 0 1),
      (∫ x, f x * ψ x ∂μ) ≤ (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
    intro n ℓ μ _ p hp f ψ hf hfnonneg hψmeas hψ
    let q := Real.conjExponent p
    have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
    have hψLp : MemLp ψ (ENNReal.ofReal q) μ :=
      MemLp.of_bound hψmeas 1 (Eventually.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (hψ x).1]
        exact (hψ x).2)
    have hψint : Integrable ψ μ := hψLp.integrable (by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hpq.symm.lt.le)
    have hψpowint : Integrable (fun x ↦ ψ x ^ q) μ := by
      have h := hψLp.integrable_norm_rpow'
      simpa only [ENNReal.toReal_ofReal hpq.symm.nonneg,
        Real.norm_of_nonneg (hψ _).1] using h
    have hpowle : (∫ x, ψ x ^ q ∂μ) ≤ ∫ x, ψ x ∂μ :=
      integral_mono hψpowint hψint
        (fun x ↦ Real.rpow_le_self_of_le_one (hψ x).1 (hψ x).2 hpq.symm.lt.le)
    have hexp : 1 / q = 1 - 1 / p := by
      simpa only [one_div] using hpq.one_sub_inv.symm
    calc
      _ ≤ (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ^ q ∂μ) ^ (1 / q) :=
        integral_mul_le_Lp_mul_Lq_of_nonneg hpq
          (Eventually.of_forall hfnonneg) (Eventually.of_forall fun x ↦ (hψ x).1) hf hψLp
      _ ≤ (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 / q) := by
        apply mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (integral_nonneg fun x ↦
            Real.rpow_nonneg (hψ x).1 _) hpowle hpq.symm.one_div_nonneg)
        exact Real.rpow_nonneg (integral_nonneg fun x ↦
          Real.rpow_nonneg (hfnonneg x) _) _
      _ = _ := by rw [hexp]

  -- Integrating a derivative comparison on a compact interval.
  have dm_sub_le_sub_of_hasDerivAt_le : ∀ {a b : ℝ} (hab : a ≤ b) {f g f' g' : ℝ → ℝ}
      (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
      (hle : ∀ t ∈ Icc a b, f' t ≤ g' t),
      f b - f a ≤ g b - g a := by
    intro a b hab f g f' g' hf hg hle
    have hmono : MonotoneOn (fun t ↦ g t - f t) (Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
        (fun t ht ↦ ((hg t ht).sub (hf t ht)).continuousAt.continuousWithinAt)
      · intro t ht
        exact ((hg t (interior_subset ht)).sub
          (hf t (interior_subset ht))).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [((hg t (interior_subset ht)).sub (hf t (interior_subset ht))).deriv]
        exact sub_nonneg.mpr (hle t (interior_subset ht))
    have h := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    linarith

  -- Scale derivative of a cutoff integral (finite measure), for a `C¹` profile with values in
  -- `[0,1]` vanishing beyond `A²`.
  have dm_hasDerivAt_cutoff_integral : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) [IsFiniteMeasure μ]
      (ξ : Amb n ℓ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφr : ∀ t, φ t ∈ Icc 0 1) {A : ℝ}
      (hA : 0 < A) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {ρ : ℝ} (hρ : 0 < ρ) {q : Amb n ℓ → ℝ}
      {B : ℝ} (hq : AEStronglyMeasurable q μ) (hqb : ∀ x, ‖q x‖ ≤ B),
      Integrable (fun x ↦ scaledRadialCutoffDeriv ξ φ ρ x * q x) μ ∧ HasDerivAt
        (fun t ↦ ∫ x, scaledRadialCutoff ξ φ t x * q x ∂μ)
        (∫ x, scaledRadialCutoffDeriv ξ φ ρ x * q x ∂μ) ρ := by
    intro n ℓ μ _ ξ φ hφ hφr A hA hcutoff ρ hρ q B hq hqb
    let K : Set (Amb n ℓ) := closedBall ξ (2 * ρ * A)
    have hscale : ∀ t ∈ Icc (ρ / 2) (2 * ρ), 0 < t := by
      intro t ht
      linarith [ht.1]
    have hout : ∀ t ∈ Icc (ρ / 2) (2 * ρ), ∀ x ∉ K,
        A ^ 2 < ‖x - ξ‖ ^ 2 / t ^ 2 := by
      intro t ht x hx
      have hx' : 2 * ρ * A < ‖x - ξ‖ := by
        simpa only [K, mem_closedBall, dist_eq_norm, not_le] using hx
      have htx : t * A < ‖x - ξ‖ :=
        (mul_le_mul_of_nonneg_right ht.2 hA.le).trans_lt hx'
      apply (lt_div_iff₀ (sq_pos_of_pos (hscale t ht))).mpr
      nlinarith [sq_nonneg (‖x - ξ‖ + t * A),
        mul_pos (sub_pos.mpr htx)
          (add_pos_of_nonneg_of_pos (norm_nonneg (x - ξ)) (mul_pos (hscale t ht) hA))]
    refine dm_hasDerivAt_integral_mul μ
      (F := scaledRadialCutoff ξ φ) (F' := scaledRadialCutoffDeriv ξ φ) (K := K)
      (show ρ ∈ Ioo (ρ / 2) (2 * ρ) by constructor <;> linarith)
      (isCompact_closedBall ξ (2 * ρ * A))
      (fun t ↦ hφ.continuous.comp (by fun_prop))
      (fun t ↦ by
        have hd := hφ.continuous_deriv_one
        change Continuous (fun x : Amb n ℓ ↦
          (-2 * ‖x - ξ‖ ^ 2 / t ^ 3) * deriv φ (‖x - ξ‖ ^ 2 / t ^ 2))
        fun_prop)
      ?_ ?_ ?_ hq hqb ?_
    · dsimp [scaledRadialCutoffDeriv]
      have hnorm : ContinuousOn (fun p : ℝ × Amb n ℓ ↦ ‖p.2 - ξ‖ ^ 2)
          (Icc (ρ / 2) (2 * ρ) ×ˢ K) := by fun_prop
      have hnonzero : ∀ p ∈ Icc (ρ / 2) (2 * ρ) ×ˢ K, p.1 ≠ 0 :=
        fun p hp ↦ (hscale p.1 hp.1).ne'
      exact ((continuousOn_const.mul hnorm).div (continuousOn_fst.pow 3)
        (fun p hp ↦ pow_ne_zero 3 (hnonzero p hp))).mul
        (hφ.continuous_deriv_one.continuousOn.comp
          (hnorm.div (continuousOn_fst.pow 2) (fun p hp ↦ pow_ne_zero 2 (hnonzero p hp)))
          (fun _ _ ↦ mem_univ _))
    · intro t ht x hx
      simp [scaledRadialCutoffDeriv, deriv_eq_zero_of_cutoff hcutoff (hout t ht x hx)]
    · intro t ht x
      exact hasDerivAt_scaledRadialCutoff ξ x hφ (hscale t ht).ne'
    · intro x
      rw [scaledRadialCutoff, Real.norm_eq_abs, abs_of_nonneg (hφr _).1]
      exact (hφr _).2

  -- The radial identity specialized to the scaled cutoff `ψ_t = φ(|x-y|²/t²)`: `d I(t) - t I'(t) +
  -- t D(t) = -C(t)`.
  have dm_cutoff_identity : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) [IsFiniteMeasure μ] (d : ℕ)
      (w : Amb n ℓ → ℝ) (hw : AEStronglyMeasurable w μ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
      (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) {R : ℝ}
      (hrad : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → (∀ u, R ^ 2 ≤ u → η u = 0) → ∫ x,
        ((d : ℝ) * η (‖x - y‖ ^ 2) + 2 * deriv η (‖x - y‖ ^ 2) * ‖x - y‖ ^ 2 * (1 - w x)) ∂μ = -∫ x,
        η (‖x - y‖ ^ 2) * inner ℝ (x - y) (H x) ∂μ)
      {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφr : ∀ t, φ t ∈ Icc 0 1) {A : ℝ} (hA : 0 < A)
      (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {t : ℝ} (ht : 0 < t) (htA : t * A ≤ R),
      (d : ℝ) * (∫ x, scaledRadialCutoff y φ t x ∂μ) - t * (∫ x, scaledRadialCutoffDeriv y φ t x ∂μ)
        + t * (∫ x, scaledRadialCutoffDeriv y φ t x * w x ∂μ) = -∫ x, scaledRadialCutoff y φ t x *
        inner ℝ (x - y) (H x) ∂μ := by
    intro n ℓ μ _ d w hw hw0 hw1 H y R hrad φ hφ hφr A hA hcutoff t ht htA
    let η : ℝ → ℝ := fun u ↦ φ (u / t ^ 2)
    have hη : ContDiff ℝ 1 η := hφ.comp (contDiff_id.div_const (t ^ 2))
    have hηcut : ∀ u, R ^ 2 ≤ u → η u = 0 := by
      intro u hu
      apply hcutoff
      apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
      have h1 : (t * A) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (mul_pos ht hA).le htA 2
      nlinarith [h1]
    have hηderiv : ∀ u, deriv η u = deriv φ (u / t ^ 2) / t ^ 2 := by
      intro u
      have h := ((hφ.differentiable (by simp) _).hasDerivAt).comp u
        ((hasDerivAt_id u).div_const (t ^ 2))
      simpa [η, Function.comp_def, div_eq_mul_inv] using h.deriv
    have heq := hrad η hη hηcut
    have hw' : ∀ x, ‖w x‖ ≤ 1 := fun x ↦ by
      rw [Real.norm_of_nonneg (hw0 x)]; exact hw1 x
    obtain ⟨hD1, -⟩ := dm_hasDerivAt_cutoff_integral μ y hφ hφr hA hcutoff ht
      (q := fun _ ↦ (1 : ℝ)) (B := 1) aestronglyMeasurable_const (fun _ ↦ by simp)
    obtain ⟨hDw, -⟩ := dm_hasDerivAt_cutoff_integral μ y hφ hφr hA hcutoff ht hw hw'
    have hψint : Integrable (scaledRadialCutoff y φ t) μ := by
      refine (integrable_const (1 : ℝ)).mono' ?_ (Eventually.of_forall fun x ↦ ?_)
      · exact (hφ.continuous.comp (by fun_prop :
          Continuous (fun x : Amb n ℓ ↦ ‖x - y‖ ^ 2 / t ^ 2))).aestronglyMeasurable
      · rw [scaledRadialCutoff, Real.norm_eq_abs, abs_of_nonneg (hφr _).1]
        exact (hφr _).2
    simp only [mul_one] at hD1
    have hpoint : ∀ x : Amb n ℓ, ((d : ℝ) * η (‖x - y‖ ^ 2) +
        2 * deriv η (‖x - y‖ ^ 2) * ‖x - y‖ ^ 2 * (1 - w x)) =
        (d : ℝ) * scaledRadialCutoff y φ t x - t * scaledRadialCutoffDeriv y φ t x +
          t * (scaledRadialCutoffDeriv y φ t x * w x) := by
      intro x
      rw [hηderiv, scaledRadialCutoffDeriv, scaledRadialCutoff]
      field_simp
      ring
    have hpoint2 : ∀ x : Amb n ℓ, η (‖x - y‖ ^ 2) * inner ℝ (x - y) (H x) =
        scaledRadialCutoff y φ t x * inner ℝ (x - y) (H x) := fun x ↦ rfl
    simp_rw [hpoint, hpoint2] at heq
    have e1 := integral_add ((hψint.const_mul (d : ℝ)).sub (hD1.const_mul t)) (hDw.const_mul t)
    have e2 := integral_sub (hψint.const_mul (d : ℝ)) (hD1.const_mul t)
    simp only [Pi.sub_apply, integral_const_mul] at e1 e2
    rw [e1, e2] at heq
    exact heq

  -- Scale derivative of the normalized cutoff mass `I(t)/t^d`, with the corrected (plus) sign of
  -- the mean-curvature term.
  have dm_hasDerivAt_normalized : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) [IsFiniteMeasure μ] (d : ℕ)
      (w : Amb n ℓ → ℝ) (hw : AEStronglyMeasurable w μ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
      (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) {R : ℝ}
      (hrad : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → (∀ u, R ^ 2 ≤ u → η u = 0) → ∫ x,
        ((d : ℝ) * η (‖x - y‖ ^ 2) + 2 * deriv η (‖x - y‖ ^ 2) * ‖x - y‖ ^ 2 * (1 - w x)) ∂μ = -∫ x,
        η (‖x - y‖ ^ 2) * inner ℝ (x - y) (H x) ∂μ)
      {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφr : ∀ t, φ t ∈ Icc 0 1) {A : ℝ} (hA : 0 < A)
      (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {t : ℝ} (ht : 0 < t) (htA : t * A ≤ R),
      HasDerivAt (fun τ ↦ (∫ x, scaledRadialCutoff y φ τ x ∂μ) / τ ^ d)
        ((∫ x, scaledRadialCutoffDeriv y φ t x * w x ∂μ) / t ^ d +
          (∫ x, scaledRadialCutoff y φ t x * inner ℝ (x - y) (H x) ∂μ) / t ^ (d + 1))
        t := by
    intro n ℓ μ _ d w hw hw0 hw1 H y R hrad φ hφ hφr A hA hcutoff t ht htA
    obtain ⟨-, hI⟩ := dm_hasDerivAt_cutoff_integral μ y hφ hφr hA hcutoff ht
      (q := fun _ ↦ (1 : ℝ)) (B := 1) aestronglyMeasurable_const (fun _ ↦ by simp)
    simp only [mul_one] at hI
    have hrel := dm_cutoff_identity μ d w hw hw0 hw1 H y hrad hφ hφr hA hcutoff ht htA
    have hp : HasDerivAt (fun τ : ℝ ↦ τ ^ d) (d * t ^ d / t) t := by
      convert (hasDerivAt_id t).pow d using 1
      · rfl
      · cases d with
        | zero => simp
        | succ m => simp [pow_succ, ht.ne', mul_div_assoc]
    convert hI.fun_div hp (pow_ne_zero d ht.ne') using 1
    · simp only [pow_succ]
      field_simp
      linear_combination hrel

  have dm_rpow_normalization : ∀ {a ρ p : ℝ} (d : ℕ) (ha : 0 ≤ a) (hρ : 0 < ρ),
      a ^ (1 - 1 / p) / ρ ^ d = ρ ^ (-(d : ℝ) / p) * (a / ρ ^ d) ^ (1 - 1 / p) := by
    intro a ρ p d ha hρ
    rw [Real.div_rpow ha (pow_pos hρ d).le, ← Real.rpow_natCast ρ d,
      ← Real.rpow_mul hρ.le]
    calc
      _ = a ^ (1 - 1 / p) * ρ ^ (-(d : ℝ)) := by rw [Real.rpow_neg hρ.le]; rfl
      _ = a ^ (1 - 1 / p) *
          (ρ ^ (-(d : ℝ) / p) * ρ ^ (-((d : ℝ) * (1 - 1 / p)))) := by
        rw [← Real.rpow_add hρ]
        congr 2
        ring
      _ = _ := by rw [Real.rpow_neg hρ.le]; ring

  have dm_rpow_le_one_add : ∀ {a p : ℝ} (ha : 0 ≤ a) (hp : 1 < p),
      a ^ (1 - 1 / p) ≤ 1 + a := by
    intro a p ha hp
    have he0 : 0 ≤ 1 - 1 / p := sub_nonneg.mpr ((div_le_one (by linarith)).mpr hp.le)
    have he1 : 1 - 1 / p ≤ 1 := by
      have : 0 ≤ 1 / p := by positivity
      linarith
    by_cases ha1 : a ≤ 1
    · exact (Real.rpow_le_one ha ha1 he0).trans (by linarith)
    · exact (Real.rpow_le_self_of_one_le (le_of_not_ge ha1) he1).trans (by linarith)

  have dm_lpScale_coefficient : ∀ {R ρ p : ℝ} (d : ℕ) (hR : 0 < R) (hρ : 0 < ρ),
      ρ ^ (-(d : ℝ) / p) / R ^ (1 - d / p) = R⁻¹ * (ρ / R) ^ (-(d : ℝ) / p) := by
    intro R ρ p d hR hρ
    rw [Real.div_rpow hρ.le hR.le, Real.rpow_sub hR, Real.rpow_one,
      div_div_eq_mul_div]
    simp only [neg_div]
    rw [Real.rpow_neg hR.le]
    field_simp

  -- Hölder bound for the mean-curvature error of the cutoff identity: `|C(t)|/t^{d+1} ≤ 2 κ Λ R⁻¹
  -- (t/R)^{-d/p} (1 + I(t)/t^d)`.
  have dm_holder_bound : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) [IsFiniteMeasure μ] (d : ℕ) {p : ℝ}
      (hp1 : 1 < p) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) {R κΛ : ℝ} (hR : 0 < R)
      (hLp : MemLp H (ENNReal.ofReal p) (μ.restrict (closedBall y R)))
      (hscale : R ^ (1 - (d : ℝ) / p) * (∫ x in closedBall y R, ‖H x‖ ^ p ∂μ) ^ (1 / p) ≤ κΛ)
      {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφr : ∀ t, φ t ∈ Icc 0 1) {A : ℝ} (hA : 0 < A)
      (hA2 : A ≤ 2) (hcutoff : ∀ t, A ^ 2 ≤ t → φ t = 0) {t : ℝ} (ht : 0 < t) (htA : t * A ≤ R),
      |(∫ x, scaledRadialCutoff y φ t x * inner ℝ (x - y) (H x) ∂μ) / t ^ (d + 1)| ≤ 2 * κΛ * R⁻¹ *
        (t / R) ^ (-(d : ℝ) / p) * (1 + (∫ x, scaledRadialCutoff y φ t x ∂μ) / t ^ d) := by
    intro n ℓ μ _ d p hp1 H y R κΛ hR hLp hscale φ hφ hφr A hA hA2 hcutoff t ht htA
    let ψ := scaledRadialCutoff y φ t
    have hψcont : Continuous ψ := by
      dsimp [ψ, scaledRadialCutoff]
      exact hφ.continuous.comp (by fun_prop)
    have hψrange : ∀ x, ψ x ∈ Icc 0 1 := fun x ↦ hφr _
    have hψzero : ∀ x, x ∉ closedBall y R → ψ x = 0 := by
      intro x hx
      apply scaledRadialCutoff_eq_zero_of_notMem_closedBall y hA hcutoff ht
      exact fun h ↦ hx (closedBall_subset_closedBall htA h)
    have hHint : Integrable (fun x ↦ ‖H x‖) (μ.restrict (closedBall y R)) :=
      (hLp.integrable (by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1.le)).norm
    have hprodint : Integrable (fun x ↦ ‖H x‖ * ψ x) (μ.restrict (closedBall y R)) :=
      hHint.mul_bdd hψcont.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (hψrange x).1]
        exact (hψrange x).2)
    have hbound : ∀ x, ‖ψ x * inner ℝ (x - y) (H x)‖ ≤ t * A * (‖H x‖ * ψ x) := by
      intro x
      by_cases hx : x ∈ closedBall y (t * A)
      · rw [norm_mul, Real.norm_of_nonneg (hψrange x).1]
        have hr : ‖x - y‖ ≤ t * A := by simpa only [mem_closedBall, dist_eq_norm] using hx
        calc
          ψ x * ‖inner ℝ (x - y) (H x)‖ ≤ ψ x * (t * A * ‖H x‖) :=
            mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_right hr (norm_nonneg _))) (hψrange x).1
          _ = _ := by ring
      · have hz := scaledRadialCutoff_eq_zero_of_notMem_closedBall y hA hcutoff ht hx
        change ψ x = 0 at hz
        simp only [hz, zero_mul, mul_zero, norm_zero, le_refl]
    have hCeq : (∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ) =
        ∫ x in closedBall y R, ψ x * inner ℝ (x - y) (H x) ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ by rw [hψzero x hx, zero_mul])).symm
    have habs : |∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ| ≤
        t * A * ∫ x in closedBall y R, ‖H x‖ * ψ x ∂μ := by
      rw [hCeq]
      have h := norm_integral_le_of_norm_le
        (hprodint.const_mul (t * A)) (Eventually.of_forall hbound)
      rw [integral_const_mul] at h
      simpa only [Real.norm_eq_abs] using h
    have hholder := dm_integral_mul_cutoff_le (μ.restrict (closedBall y R)) hp1
      hLp.norm (fun x ↦ norm_nonneg (H x)) hψcont.aestronglyMeasurable hψrange
    have hmass : (∫ x in closedBall y R, ψ x ∂μ) = ∫ x, ψ x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hψzero
    rw [hmass] at hholder
    have hmass0 : 0 ≤ ∫ x, ψ x ∂μ := integral_nonneg fun x ↦ (hψrange x).1
    have hnorm0 : 0 ≤ (∫ x, ψ x ∂μ) / t ^ d := div_nonneg hmass0 (pow_pos ht d).le
    set L := (∫ x in closedBall y R, ‖H x‖ ^ p ∂μ) ^ (1 / p) with hL
    have hL0 : 0 ≤ L := Real.rpow_nonneg (integral_nonneg fun x ↦
      Real.rpow_nonneg (norm_nonneg _) _) _
    have hscale' : L ≤ κΛ / R ^ (1 - (d : ℝ) / p) := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hR _), mul_comm]
      exact hscale
    have hstep1 : |(∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ) / t ^ (d + 1)| ≤
        A / t ^ d * L * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
      rw [abs_div, abs_of_pos (pow_pos ht (d + 1))]
      calc
        _ ≤ (t * A * ∫ x in closedBall y R, ‖H x‖ * ψ x ∂μ) / t ^ (d + 1) :=
          div_le_div_of_nonneg_right habs (pow_pos ht _).le
        _ ≤ (t * A * (L * (∫ x, ψ x ∂μ) ^ (1 - 1 / p))) / t ^ (d + 1) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hholder (mul_pos ht hA).le) (pow_pos ht _).le
        _ = _ := by rw [pow_succ]; field_simp
    calc
      _ ≤ A / t ^ d * L * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := hstep1
      _ = A * L * ((∫ x, ψ x ∂μ) ^ (1 - 1 / p) / t ^ d) := by ring
      _ = A * t ^ (-(d : ℝ) / p) * L * ((∫ x, ψ x ∂μ) / t ^ d) ^ (1 - 1 / p) := by
        rw [dm_rpow_normalization d hmass0 ht]
        ring
      _ ≤ A * t ^ (-(d : ℝ) / p) * L * (1 + (∫ x, ψ x ∂μ) / t ^ d) :=
        mul_le_mul_of_nonneg_left (dm_rpow_le_one_add hnorm0 hp1) (by positivity)
      _ ≤ (2 * t ^ (-(d : ℝ) / p) * (κΛ / R ^ (1 - (d : ℝ) / p))) *
          (1 + (∫ x, ψ x ∂μ) / t ^ d) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul
          (mul_le_mul_of_nonneg_right hA2 (Real.rpow_pos_of_pos ht _).le) hscale' hL0
        positivity
      _ = 2 * κΛ * (t ^ (-(d : ℝ) / p) / R ^ (1 - (d : ℝ) / p)) *
          (1 + (∫ x, ψ x ∂μ) / t ^ d) := by ring
      _ = _ := by rw [dm_lpScale_coefficient d hR ht]; ring

  -- Pointwise comparison of the defect integrands on the derivative support: `ψ'_t w / t^d ≤
  -- (1+ε)^d ψ'_t w / max(s,|x-y|)^d` for `s ≤ t`.
  have dm_defect_bound : ∀ {n ℓ : ℕ} (ξ x : Amb n ℓ) (d : ℕ) {w : ℝ} (hw0 : 0 ≤ w) {ε s t : ℝ}
      (hε : 0 < ε) (hs : 0 < s) (hst : s ≤ t),
      scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t x * w / t ^ d ≤ (1 + ε) ^ d *
        (scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t x * (w / (max s ‖x - ξ‖) ^ d)) := by
    intro n ℓ ξ x d w hw0 ε s t hε hs hst
    by_cases hz : scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t x = 0
    · simp [hz]
    have ht : 0 < t := hs.trans_le hst
    obtain ⟨hrlo, hrhi⟩ := scaledRadialCutoffDeriv_support ξ x hε ht hz
    have hr : 0 < ‖x - ξ‖ := ht.trans_le hrlo
    have hpowhi := pow_le_pow_left₀ (norm_nonneg (x - ξ)) hrhi d
    rw [mul_pow] at hpowhi
    have hzpos : 0 ≤ scaledRadialCutoffDeriv ξ (monotonicityCutoff ε) t x * w :=
      mul_nonneg (scaledRadialCutoffDeriv_nonneg ξ x (monotonicityCutoff_antitone hε) ht) hw0
    rw [max_eq_right (hst.trans hrlo), ← mul_div_assoc, ← mul_div_assoc]
    apply (div_le_div_iff₀ (pow_pos ht d) (pow_pos hr d)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpowhi hzpos]

  -- **Core monotonicity.** From the radial first-variation identity and the `Lᵖ` smallness of `H`,
  -- the explicit factors `F^± = exp(±Λ/2 (t/R)^{1-d/p})` give `F⁺(s)(1 + a(s)) ≤ F⁺(r)(1 + a(r))`
  -- and `F⁻(r)(1 + a(r)) - F⁻(s)(1 + a(s)) ≤ ∫_{B_r(y) \ B_s(y)} w / |x - y|^d`, `a(t) =
  -- μ(B_t(y))/t^d`.
  have dm_core : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) [IsFiniteMeasure μ] (d : ℕ) {p : ℝ}
      (hp : (d : ℝ) < p) (hp1 : 1 < p) (w : Amb n ℓ → ℝ) (hw : AEStronglyMeasurable w μ)
      (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) {R Λ : ℝ}
      (hR : 0 < R) (hΛ : 0 ≤ Λ) (hLp : MemLp H (ENNReal.ofReal p) (μ.restrict (closedBall y R)))
      (hscale : R ^ (1 - (d : ℝ) / p) * (∫ x in closedBall y R, ‖H x‖ ^ p ∂μ) ^ (1 / p) ≤
        lpMeanCurvatureKappa d p * Λ)
      (hrad : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → (∀ u, R ^ 2 ≤ u → η u = 0) → ∫ x,
        ((d : ℝ) * η (‖x - y‖ ^ 2) + 2 * deriv η (‖x - y‖ ^ 2) * ‖x - y‖ ^ 2 * (1 - w x)) ∂μ = -∫ x,
        η (‖x - y‖ ^ 2) * inner ℝ (x - y) (H x) ∂μ)
      {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hrR : r < R),
      lpMonotonicityFactor d p R Λ s * (1 + μ.real (closedBall y s) / s ^ d) ≤ lpMonotonicityFactor
        d p R Λ r * (1 + μ.real (closedBall y r) / r ^ d) ∧ lpMonotonicityFactor d p R (-Λ) r *
        (1 + μ.real (closedBall y r) / r ^ d) - lpMonotonicityFactor d p R (-Λ) s *
        (1 + μ.real (closedBall y s) / s ^ d) ≤ ∫ x in closedBall y r \ closedBall y s, w x /
        ‖x - y‖ ^ d ∂μ := by
    intro n ℓ μ _ d p hp hp1 w hw hw0 hw1 H y R Λ hR hΛ hLp hscale hrad s r hs hsr hrR
    have hp0 : 0 < p := by linarith
    have hr : 0 < r := hs.trans_le hsr
    set κ := lpMeanCurvatureKappa d p with hκdef
    set Fp : ℝ → ℝ := lpMonotonicityFactor d p R Λ with hFp
    set Fm : ℝ → ℝ := lpMonotonicityFactor d p R (-Λ) with hFm
    -- the truncated defect weight
    set q : Amb n ℓ → ℝ := fun x ↦ w x / (max s ‖x - y‖) ^ d with hqdef
    have hq : AEStronglyMeasurable q μ :=
      (hw.aemeasurable.div ((continuous_const.max
        (by fun_prop : Continuous fun x : Amb n ℓ ↦ ‖x - y‖)).pow
          d).measurable.aemeasurable).aestronglyMeasurable
    have hqnn : ∀ x, 0 ≤ q x := fun x ↦
      div_nonneg (hw0 x) (pow_nonneg (hs.le.trans (le_max_left _ _)) d)
    have hqb : ∀ x, ‖q x‖ ≤ (s ^ d)⁻¹ := by
      intro x
      have hm : 0 < max s ‖x - y‖ := hs.trans_le (le_max_left _ _)
      rw [Real.norm_of_nonneg (hqnn x)]
      show w x / (max s ‖x - y‖) ^ d ≤ (s ^ d)⁻¹
      rw [div_eq_mul_inv]
      calc w x * ((max s ‖x - y‖) ^ d)⁻¹ ≤ 1 * ((max s ‖x - y‖) ^ d)⁻¹ :=
            mul_le_mul_of_nonneg_right (hw1 x) (inv_nonneg.mpr (pow_pos hm d).le)
        _ ≤ (s ^ d)⁻¹ := by
            rw [one_mul]
            exact inv_anti₀ (pow_pos hs d) (pow_le_pow_left₀ hs.le (le_max_left _ _) d)
    have hw' : ∀ x, ‖w x‖ ≤ 1 := fun x ↦ by rw [Real.norm_of_nonneg (hw0 x)]; exact hw1 x
    -- abbreviations for the `ε`-level quantities
    set I : ℝ → ℝ → ℝ := fun ε t ↦ ∫ x, scaledRadialCutoff y (monotonicityCutoff ε) t x ∂μ
      with hIdef
    set G : ℝ → ℝ → ℝ := fun ε t ↦
      ∫ x, scaledRadialCutoff y (monotonicityCutoff ε) t x * q x ∂μ with hGdef
    -- the fixed-`ε` inequalities
    have hfixed : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → (1 + ε) * r ≤ R →
        Fp s * (1 + I ε s / s ^ d) ≤ Fp r * (1 + I ε r / r ^ d) ∧
        Fm r * (1 + I ε r / r ^ d) - Fm s * (1 + I ε s / s ^ d) ≤
          (1 + ε) ^ d * (G ε r - G ε s) := by
      intro ε hε hε1 hεr
      have hA : 0 < 1 + ε := by linarith
      have hA2 : 1 + ε ≤ 2 := by linarith
      have hφ := contDiff_monotonicityCutoff ε
      have hφr := monotonicityCutoff_mem_Icc ε
      have hcut := monotonicityCutoff_cutoff hε
      have htpos : ∀ t ∈ Icc s r, 0 < t := fun t ht ↦ hs.trans_le ht.1
      have htA : ∀ t ∈ Icc s r, t * (1 + ε) ≤ R := fun t ht ↦ by
        have := mul_le_mul_of_nonneg_right ht.2 hA.le
        linarith [mul_comm r (1 + ε)]
      -- the pieces at each scale
      set N : ℝ → ℝ := fun t ↦
        (∫ x, scaledRadialCutoffDeriv y (monotonicityCutoff ε) t x * w x ∂μ) / t ^ d with hNdef
      set Er : ℝ → ℝ := fun t ↦
        (∫ x, scaledRadialCutoff y (monotonicityCutoff ε) t x * inner ℝ (x - y) (H x) ∂μ) /
          t ^ (d + 1) with hErdef
      set B : ℝ → ℝ := fun t ↦ 2 * κ * Λ * R⁻¹ * (t / R) ^ (-(d : ℝ) / p) with hBdef
      set G' : ℝ → ℝ := fun t ↦
        ∫ x, scaledRadialCutoffDeriv y (monotonicityCutoff ε) t x * q x ∂μ with hG'def
      have hM : ∀ t ∈ Icc s r, HasDerivAt (fun τ ↦ I ε τ / τ ^ d) (N t + Er t) t := fun t ht ↦
        dm_hasDerivAt_normalized μ d w hw hw0 hw1 H y hrad hφ hφr hA hcut (htpos t ht) (htA t ht)
      have hE : ∀ t ∈ Icc s r, |Er t| ≤ B t * (1 + I ε t / t ^ d) := by
        intro t ht
        have h := dm_holder_bound μ d hp1 H y hR hLp hscale hφ hφr hA hA2 hcut (htpos t ht)
          (htA t ht)
        calc |Er t| ≤ 2 * (κ * Λ) * R⁻¹ * (t / R) ^ (-(d : ℝ) / p) * (1 + I ε t / t ^ d) := h
          _ = B t * (1 + I ε t / t ^ d) := by simp only [hBdef]; ring
      have hB0 : ∀ t ∈ Icc s r, 0 ≤ B t := fun t ht ↦ by
        have := htpos t ht
        have : 0 ≤ κ := (lpMeanCurvatureKappa_pos hp).le
        positivity
      have hI0 : ∀ t ∈ Icc s r, 0 ≤ I ε t / t ^ d := fun t ht ↦
        div_nonneg (integral_nonneg fun x ↦ (hφr _).1) (pow_pos (htpos t ht) d).le
      have hG : ∀ t ∈ Icc s r, HasDerivAt (G ε) (G' t) t := fun t ht ↦
        (dm_hasDerivAt_cutoff_integral μ y hφ hφr hA hcut (htpos t ht) hq hqb).2
      have hN0 : ∀ t ∈ Icc s r, 0 ≤ N t := by
        intro t ht
        apply div_nonneg _ (pow_pos (htpos t ht) d).le
        exact integral_nonneg fun x ↦ mul_nonneg
          (scaledRadialCutoffDeriv_nonneg y x (monotonicityCutoff_antitone hε) (htpos t ht))
          (hw0 x)
      have hNG : ∀ t ∈ Icc s r, N t ≤ (1 + ε) ^ d * G' t := by
        intro t ht
        have hint1 := (dm_hasDerivAt_cutoff_integral μ y hφ hφr hA hcut (htpos t ht) hw hw').1
        have hint2 := (dm_hasDerivAt_cutoff_integral μ y hφ hφr hA hcut (htpos t ht) hq hqb).1
        simp only [hNdef, hG'def]
        rw [← integral_div, ← integral_const_mul]
        apply integral_mono (hint1.div_const _) (hint2.const_mul _)
        intro x
        exact dm_defect_bound y x d (hw0 x) hε hs ht.1
      have hFp' : ∀ t ∈ Icc s r, HasDerivAt Fp (Fp t * B t) t := by
        intro t ht
        have h := hasDerivAt_lpMonotonicityFactor (n := d) hp0 hR (htpos t ht) Λ
        simpa only [hFp, hBdef] using h
      have hFm' : ∀ t ∈ Icc s r, HasDerivAt Fm (Fm t * (-B t)) t := by
        intro t ht
        have h := hasDerivAt_lpMonotonicityFactor (n := d) hp0 hR (htpos t ht) (-Λ)
        have e : 2 * lpMeanCurvatureKappa d p * -Λ * R⁻¹ * (t / R) ^ (-(d : ℝ) / p) = -B t := by
          simp only [hBdef]; ring
        rw [e] at h
        simpa only [hFm] using h
      have hFppos : ∀ t, 0 < Fp t := fun t ↦ Real.exp_pos _
      have hFmpos : ∀ t, 0 < Fm t := fun t ↦ Real.exp_pos _
      have hFm1 : ∀ t ∈ Icc s r, Fm t ≤ 1 := by
        intro t ht
        simp only [hFm, lpMonotonicityFactor]
        apply Real.exp_le_one_iff.mpr
        have : 0 ≤ (t / R) ^ (1 - (d : ℝ) / p) :=
          Real.rpow_nonneg (div_pos (htpos t ht) hR).le _
        nlinarith
      constructor
      · -- `F⁺ (1 + M)` is nondecreasing on `[s, r]`
        have h := dm_sub_le_sub_of_hasDerivAt_le hsr
          (f := fun _ ↦ (0 : ℝ)) (g := fun t ↦ Fp t * (1 + I ε t / t ^ d))
          (f' := fun _ ↦ 0)
          (g' := fun t ↦ Fp t * B t * (1 + I ε t / t ^ d) + Fp t * (N t + Er t))
          (fun t _ ↦ hasDerivAt_const t 0)
          (fun t ht ↦ by
            exact (hFp' t ht).fun_mul ((hM t ht).const_add 1))
          (fun t ht ↦ by
            have h1 := hE t ht
            have h2 := hN0 t ht
            have h3 : 0 ≤ B t * (1 + I ε t / t ^ d) + Er t + N t := by
              have := neg_abs_le (Er t)
              linarith
            have h4 := mul_nonneg (hFppos t).le h3
            linarith)
        linarith
      · -- `F⁻ (1 + M) - (1 + ε)^d G` is nonincreasing on `[s, r]`
        have h := dm_sub_le_sub_of_hasDerivAt_le hsr
          (f := fun t ↦ Fm t * (1 + I ε t / t ^ d)) (g := fun t ↦ (1 + ε) ^ d * G ε t)
          (f' := fun t ↦ Fm t * (-B t) * (1 + I ε t / t ^ d) + Fm t * (N t + Er t))
          (g' := fun t ↦ (1 + ε) ^ d * G' t)
          (fun t ht ↦ by
            exact (hFm' t ht).fun_mul ((hM t ht).const_add 1))
          (fun t ht ↦ (hG t ht).const_mul _)
          (fun t ht ↦ by
            have h1 := hE t ht
            have h2 := hN0 t ht
            have h3 : Er t - B t * (1 + I ε t / t ^ d) ≤ 0 := by
              have := le_abs_self (Er t)
              linarith
            have h4 := mul_nonpos_of_nonneg_of_nonpos (hFmpos t).le h3
            have h5 : Fm t * N t ≤ N t := mul_le_of_le_one_left h2 (hFm1 t ht)
            have h6 := hNG t ht
            linarith)
        linarith
    -- passage to the limit `ε ↓ 0`
    have hε₀ : 0 < min 1 (R / r - 1) := lt_min one_pos (by
      rw [sub_pos, one_lt_div hr]; exact hrR)
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 ∧ (1 + ε) * r ≤ R := by
      filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
      refine ⟨hε.1, hε.2.le.trans (min_le_left _ _), ?_⟩
      have h1 : ε ≤ R / r - 1 := hε.2.le.trans (min_le_right _ _)
      have h2 : (1 + ε) ≤ R / r := by linarith
      calc (1 + ε) * r ≤ R / r * r := mul_le_mul_of_nonneg_right h2 hr.le
        _ = R := div_mul_cancel₀ R hr.ne'
    have hIlim : ∀ t, 0 < t → Tendsto (fun ε ↦ I ε t) (𝓝[>] (0 : ℝ))
        (𝓝 (μ.real (closedBall y t))) := by
      intro t ht
      have h := dm_tendsto_integral_cutoff μ y ht (q := fun _ ↦ (1 : ℝ)) (B := 1)
        aestronglyMeasurable_const (fun _ ↦ by simp)
      simpa only [mul_one, setIntegral_const, smul_eq_mul] using h
    have hGlim : ∀ t, 0 < t → Tendsto (fun ε ↦ G ε t) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ x in closedBall y t, q x ∂μ)) := fun t ht ↦
      dm_tendsto_integral_cutoff μ y ht hq hqb
    have hMlim : ∀ t, 0 < t → ∀ F : ℝ, Tendsto (fun ε ↦ F * (1 + I ε t / t ^ d)) (𝓝[>] (0 : ℝ))
        (𝓝 (F * (1 + μ.real (closedBall y t) / t ^ d))) := fun t ht F ↦
      (((hIlim t ht).div_const (t ^ d)).const_add 1).const_mul F
    have hpow : Tendsto (fun ε : ℝ ↦ (1 + ε) ^ d) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_id.mono_left inf_le_left)
      simpa only [add_zero, one_pow] using h.pow d
    constructor
    · apply le_of_tendsto_of_tendsto (hMlim s hs (Fp s)) (hMlim r hr (Fp r))
      filter_upwards [hev] with ε hε
      exact (hfixed ε hε.1 hε.2.1 hε.2.2).1
    · have hlim1 := (hMlim r hr (Fm r)).sub (hMlim s hs (Fm s))
      have hlim2 := hpow.mul ((hGlim r hr).sub (hGlim s hs))
      have hle := le_of_tendsto_of_tendsto hlim1 hlim2 (by
        filter_upwards [hev] with ε hε
        exact (hfixed ε hε.1 hε.2.1 hε.2.2).2)
      rw [one_mul] at hle
      have hqint : IntegrableOn q (closedBall y r) μ :=
        (integrable_const (s ^ d)⁻¹).integrableOn.mono' hq.restrict
          (Eventually.of_forall hqb)
      rw [← setIntegral_sdiff measurableSet_closedBall hqint
        (closedBall_subset_closedBall hsr)] at hle
      refine hle.trans (le_of_eq ?_)
      apply setIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
      intro x hx
      have hxs : s < ‖x - y‖ := by
        simpa only [mem_closedBall, dist_eq_norm, not_le] using hx.2
      simp only [hqdef, max_eq_right hxs.le]

  -- `p_x` is an orthogonal projection or `0`, so `|v - p_x v| ≤ |v|`.
  have dm_norm_sub_tangentProj_le : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
      (x v : Amb n ℓ),
      ‖v - V.tangentProj x v‖ ≤ ‖v‖ := by
    intro n ℓ U V x v
    unfold RectifiableVarifold.tangentProj
    split_ifs with h
    · rw [← Submodule.starProjection_orthogonal_val]
      exact Submodule.norm_starProjection_apply_le _ v
    · simp

  -- The radial first-variation identity for the contract's varifold, with the squared-radius vector
  -- field `X(x) = η(|x-y|²)(x-y)` and `w = |p_x^⊥(x-y)|²/|x-y|²`.
  have dm_radial_identity : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
      (H : Amb n ℓ → Amb n ℓ) (hH : V.HasGeneralizedMeanCurvature H)
      (hproj : ∀ᵐ x ∂V.weight, ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ V.tangentProj x
        = T.starProjection)
      (y : Amb n ℓ) {R : ℝ} (hR : 0 ≤ R) (hball : closedBall y R ⊆ U) (η : ℝ → ℝ)
      (hη : ContDiff ℝ 1 η) (hcut : ∀ u, R ^ 2 ≤ u → η u = 0),
      ∫ x,
        ((n : ℝ) * η (‖x - y‖ ^ 2) + 2 * deriv η (‖x - y‖ ^ 2) * ‖x - y‖ ^ 2 *
          (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2))
        ∂V.weight = -∫ x, η (‖x - y‖ ^ 2) * inner ℝ (x - y) (H x) ∂V.weight := by
    intro n ℓ U V H hH hproj y R hR hball η hη hcut
    have hX := contDiff_squaredRadialVectorField y hη
    have hXc := hasCompactSupport_squaredRadialVectorField y hR hcut
    have hXs := (tsupport_squaredRadialVectorField_subset_closedBall y hR hcut).trans hball
    have heq := hH.2 _ hX hXc hXs
    have hae : (fun x ↦ V.divM (squaredRadialVectorField y η) x) =ᵐ[V.weight]
        (fun x ↦ (n : ℝ) * η (‖x - y‖ ^ 2) + 2 * deriv η (‖x - y‖ ^ 2) * ‖x - y‖ ^ 2 *
          (1 - ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ 2)) := by
      filter_upwards [hproj] with x hx
      obtain ⟨T, hT, hPx⟩ := hx
      have hd : HasDerivAt η (deriv η (‖x - y‖ ^ 2)) (‖x - y‖ ^ 2) :=
        (hη.differentiable (by simp) _).hasDerivAt
      rw [RectifiableVarifold.divM, (hasFDerivAt_squaredRadialVectorField y x hd).fderiv, hPx,
        trace_radialEndomorphism, hT, innerSL_apply_apply, inner_starProjection_eq_norm_sq]
      have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection (x - y) T
      rw [Submodule.starProjection_orthogonal_val] at hpy
      by_cases hxy : ‖x - y‖ = 0
      · have h0 : x - y = 0 := norm_eq_zero.mp hxy
        simp [h0, mul_comm]
      · have hxy2 : ‖x - y‖ ^ 2 ≠ 0 := pow_ne_zero 2 hxy
        have e : ‖x - y‖ ^ 2 * (1 - ‖x - y - T.starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) =
            ‖x - y‖ ^ 2 - ‖x - y - T.starProjection (x - y)‖ ^ 2 := by
          field_simp
        rw [mul_assoc (2 * deriv η (‖x - y‖ ^ 2)), e]
        linear_combination (-2 * deriv η (‖x - y‖ ^ 2)) * hpy
    rw [integral_congr_ae hae] at heq
    simpa only [squaredRadialVectorField, real_inner_smul_left] using heq

  -- The core monotonicity inequalities for the contract's varifold at any closed ball `B_R(c) ⊆
  -- B_ρ(0)`, with `κ Λ = δ`.
  have dm_varifold_core : ∀ {n ℓ : ℕ} {p : ℝ} (hp : (n : ℝ) < p) (hp1 : 1 < p) {U : Set (Amb n ℓ)}
      (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (hH : V.HasGeneralizedMeanCurvature H)
      (hPmeas : AEStronglyMeasurable V.tangentProj V.weight)
      (hproj : ∀ᵐ x ∂V.weight, ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ V.tangentProj x
        = T.starProjection)
      {δ ρ Λ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hκΛ : lpMeanCurvatureKappa n p * Λ = δ)
      (hBU : closedBall (0 : Amb n ℓ) ρ ⊆ U) (hfin : V.weight (closedBall 0 ρ) < ∞)
      (hLp : V.scaledLpNorm H p 0 ρ ≤ ENNReal.ofReal δ) (c : Amb n ℓ) {R : ℝ} (hR : 0 < R)
      (hcR : ‖c‖ + R ≤ ρ) {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hrR : r < R),
      lpMonotonicityFactor n p R Λ s * (1 + V.weight.real (closedBall c s) / s ^ n) ≤
        lpMonotonicityFactor n p R Λ r * (1 + V.weight.real (closedBall c r) / r ^ n) ∧
        lpMonotonicityFactor n p R (-Λ) r * (1 + V.weight.real (closedBall c r) / r ^ n) -
        lpMonotonicityFactor n p R (-Λ) s * (1 + V.weight.real (closedBall c s) / s ^ n) ≤ ∫ x in
        closedBall c r \ closedBall c s, ‖(x - c) - V.tangentProj x (x - c)‖ ^ 2 / ‖x - c‖ ^ (n + 2)
        ∂V.weight := by
    intro n ℓ p hp hp1 U V H hH hPmeas hproj δ ρ Λ hρ hδ hΛ hκΛ hBU hfin hLp c R hR hcR s r hs hsr
      hrR
    have hp0 : 0 < p := by linarith
    have hpn : 0 < p - n := sub_pos.mpr hp
    set ν := V.weight.restrict (closedBall (0 : Amb n ℓ) ρ) with hνdef
    have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hfin.ne
    have hsub : closedBall c R ⊆ closedBall (0 : Amb n ℓ) ρ := by
      intro x hx
      rw [mem_closedBall, dist_eq_norm] at hx
      rw [mem_closedBall, dist_zero_right]
      calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ R + ‖c‖ := by linarith
        _ ≤ ρ := by linarith
    have hνrestr : ∀ A : Set (Amb n ℓ), MeasurableSet A → A ⊆ closedBall 0 ρ →
        ν.restrict A = V.weight.restrict A := by
      intro A hA hAsub
      rw [hνdef, Measure.restrict_restrict hA, inter_eq_left.mpr hAsub]
    have hνreal : ∀ t, t ≤ R → ν.real (closedBall c t) = V.weight.real (closedBall c t) := by
      intro t ht
      rw [measureReal_def, measureReal_def, hνdef, Measure.restrict_apply measurableSet_closedBall,
        inter_eq_left.mpr ((closedBall_subset_closedBall ht).trans hsub)]
    have hνint : ∀ f : Amb n ℓ → ℝ, (∀ x, x ∉ closedBall c R → f x = 0) →
        ∫ x, f x ∂ν = ∫ x, f x ∂V.weight := by
      intro f hf
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ hf x (fun h ↦ hx (hsub h)))
    -- the weight `w`
    set w : Amb n ℓ → ℝ := fun x ↦ ‖(x - c) - V.tangentProj x (x - c)‖ ^ 2 / ‖x - c‖ ^ 2
      with hwdef
    have hw0 : ∀ x, 0 ≤ w x := fun x ↦ by positivity
    have hw1 : ∀ x, w x ≤ 1 := by
      intro x
      by_cases hx : ‖x - c‖ = 0
      · simp [hwdef, hx]
      · apply div_le_one_of_le₀ _ (sq_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _) (dm_norm_sub_tangentProj_le V x (x - c)) 2
    have hwm : AEStronglyMeasurable w V.weight := by
      have happ : Continuous (Function.uncurry
          fun (A : Amb n ℓ →L[ℝ] Amb n ℓ) (v : Amb n ℓ) ↦ A v) :=
        continuous_fst.clm_apply continuous_snd
      have hTm : AEStronglyMeasurable (fun x ↦ V.tangentProj x (x - c)) V.weight :=
        happ.comp_aestronglyMeasurable₂ hPmeas (continuous_sub_right c).aestronglyMeasurable
      have h1 : AEStronglyMeasurable (fun x ↦ ‖(x - c) - V.tangentProj x (x - c)‖ ^ 2) V.weight :=
        ((continuous_sub_right c).aestronglyMeasurable.sub hTm).norm.pow 2
      have h2 : AEStronglyMeasurable (fun x : Amb n ℓ ↦ ‖x - c‖ ^ 2) V.weight :=
        ((continuous_sub_right c).norm.pow 2).aestronglyMeasurable
      exact (h1.aemeasurable.div h2.aemeasurable).aestronglyMeasurable
    -- the radial identity, for `ν`
    have hrad : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → (∀ u, R ^ 2 ≤ u → η u = 0) →
        ∫ x, ((n : ℝ) * η (‖x - c‖ ^ 2) + 2 * deriv η (‖x - c‖ ^ 2) * ‖x - c‖ ^ 2 *
          (1 - w x)) ∂ν = -∫ x, η (‖x - c‖ ^ 2) * inner ℝ (x - c) (H x) ∂ν := by
      intro η hη hcut
      have hout : ∀ x, x ∉ closedBall c R → R ^ 2 < ‖x - c‖ ^ 2 := by
        intro x hx
        have h : R < ‖x - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
        exact pow_lt_pow_left₀ h hR.le two_ne_zero
      rw [hνint _ (fun x hx ↦ by
            simp [hcut _ (hout x hx).le, deriv_eq_zero_of_cutoff hcut (hout x hx)]),
        hνint _ (fun x hx ↦ by simp [hcut _ (hout x hx).le])]
      exact dm_radial_identity V H hH hproj c hR.le (hsub.trans hBU) η hη hcut
    -- `Lᵖ` bounds
    have hLp' := hLp
    simp only [RectifiableVarifold.scaledLpNorm] at hLp'
    set LI := ∫⁻ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ₑ ^ p ∂V.weight with hLI
    set LR := ∫⁻ x in closedBall c R, ‖H x‖ₑ ^ p ∂V.weight with hLR
    have hρpos : 0 < ρ ^ (p - n) := Real.rpow_pos_of_pos hρ _
    have hLIfin : LI ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hρpos).ne',
        ENNReal.top_rpow_of_pos (one_div_pos.mpr hp0)] at hLp'
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hLp')
    have hLRle : LR ≤ LI := lintegral_mono_set hsub
    have hLRfin : LR ≠ ⊤ := ne_top_of_le_ne_top hLIfin hLRle
    have hRρ : R ≤ ρ := by linarith [norm_nonneg c]
    have hscaleE : (ENNReal.ofReal (R ^ (p - n)) * LR) ^ (1 / p) ≤ ENNReal.ofReal δ := by
      refine le_trans (ENNReal.rpow_le_rpow ?_ (one_div_pos.mpr hp0).le) hLp'
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow hR.le hRρ hpn.le)) hLRle
    have hHmeas : AEStronglyMeasurable H (V.weight.restrict (closedBall c R)) :=
      (hH.1.integrableOn_compact_subset (hsub.trans hBU)
        (isCompact_closedBall c R)).aestronglyMeasurable
    have hpE0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
    have hpEtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
    have hpE : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
    have hMemLp : MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall c R)) := by
      have hlt : eLpNorm H (ENNReal.ofReal p) (V.weight.restrict (closedBall c R)) < ⊤ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpE0 hpEtop hHmeas, hpE]
        exact ENNReal.rpow_lt_top_of_nonneg (one_div_pos.mpr hp0).le hLRfin
      exact hlt
    have hJint : Integrable (fun x ↦ ‖H x‖ ^ p) (V.weight.restrict (closedBall c R)) := by
      have h := hMemLp.integrable_norm_rpow hpE0 hpEtop
      rwa [hpE] at h
    set J := ∫ x in closedBall c R, ‖H x‖ ^ p ∂V.weight with hJ
    have hJ0 : 0 ≤ J := integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
    have hLRJ : LR = ENNReal.ofReal J := by
      rw [hJ, ofReal_integral_eq_lintegral_ofReal hJint
        (Eventually.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg _) _), hLR]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm]
    have hscaleR : (R ^ (p - n) * J) ^ (1 / p) ≤ δ := by
      rw [hLRJ, ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
        ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.rpow_nonneg hR.le _) hJ0)
          (one_div_pos.mpr hp0).le] at hscaleE
      exact (ENNReal.ofReal_le_ofReal_iff hδ.le).mp hscaleE
    have hscale : R ^ (1 - (n : ℝ) / p) * (∫ x in closedBall c R, ‖H x‖ ^ p ∂ν) ^ (1 / p) ≤
        lpMeanCurvatureKappa n p * Λ := by
      rw [hκΛ, hνrestr _ measurableSet_closedBall hsub, ← hJ]
      calc R ^ (1 - (n : ℝ) / p) * J ^ (1 / p) = (R ^ (p - n) * J) ^ (1 / p) := by
            rw [Real.mul_rpow (Real.rpow_nonneg hR.le _) hJ0, ← Real.rpow_mul hR.le]
            congr 2
            field_simp
        _ ≤ δ := hscaleR
    have hLpν : MemLp H (ENNReal.ofReal p) (ν.restrict (closedBall c R)) := by
      rw [hνrestr _ measurableSet_closedBall hsub]
      exact hMemLp
    obtain ⟨h1, h2⟩ := dm_core ν n hp hp1 w (hwm.restrict) hw0 hw1 H c hR hΛ hLpν hscale hrad
      hs hsr hrR
    rw [hνreal s (hsr.trans hrR.le), hνreal r hrR.le] at h1 h2
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    rw [hνrestr _ (measurableSet_closedBall.diff measurableSet_closedBall)
      ((sdiff_subset.trans (closedBall_subset_closedBall hrR.le)).trans hsub)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [hwdef]
    rw [div_div, ← pow_add, add_comm 2 n]

  have dm_unitBallVolume_pos : ∀ (n : ℕ), 0 < unitBallVolume n := fun n ↦
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))

  -- Integration against `μ_V` is integration of `θ` against `Hⁿ ⌞ M`.
  have dm_integral_weight_eq : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
      (f : Amb n ℓ → ℝ),
      ∫ x, f x ∂V.weight = ∫ x in V.carrier, f x * V.mult x ∂(μHE[n] : Measure (Amb n ℓ)) := by
    intro n ℓ U V f
    rw [RectifiableVarifold.weight, integral_withDensity_eq_integral_toReal_smul₀
        V.aemeasurable_mult.ennreal_ofReal (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) f]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem₀ V.nullMeasurableSet_carrier] with x hx
    rw [ENNReal.toReal_ofReal (V.mult_pos x hx).le, smul_eq_mul, mul_comm]

  -- Weighted blow-up change of variables for the contract's varifold.
  have dm_integral_weighted_blowUp : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
      (ξ : Amb n ℓ) {r : ℝ} (hr : 0 < r) (f : Amb n ℓ → ℝ),
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap ξ r '' V.carrier, f y * V.mult (ξ + r • y)
        ∂(μHE[n] : Measure (Amb n ℓ)))
        = r⁻¹ ^ n * ∫ x, f (Poincare.SimonGMT.Chapter03.blowUpMap ξ r x) ∂V.weight := by
    intro n ℓ U V ξ r hr f
    let b := Poincare.SimonGMT.Chapter04.blowUpHomeomorph ξ hr
    have hi := b.symm.measurableEmbedding.integral_map
      (μ := (μHE[n] : Measure (Amb n ℓ)).restrict
        (Poincare.SimonGMT.Chapter03.blowUpMap ξ r '' V.carrier))
      (fun x ↦ f (b x) * V.mult x)
    rw [Poincare.SimonGMT.Chapter04.map_inverse_blowUp_carrier ξ hr V.carrier,
      integral_smul_measure,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_pos.mpr hr).le, smul_eq_mul] at hi
    rw [dm_integral_weight_eq V]
    simp only [Homeomorph.apply_symm_apply] at hi
    simpa only [b, Poincare.SimonGMT.Chapter04.blowUpHomeomorph_apply,
      Poincare.SimonGMT.Chapter04.blowUpHomeomorph_symm_apply] using hi.symm

  -- **Density lower bound at a weighted approximate-tangent point** (Simon Ch. 3, 1.7–1.8): if
  -- `θ(z) ≥ 1` and `t⁻ⁿ μ_V(B_t(z)) ≤ K` for all `t ∈ (0, s₀]`, then `ω_n ≤ K`.
  have dm_density_lower : ∀ {n ℓ : ℕ} (hn : 0 < n) {U : Set (Amb n ℓ)}
      (V : RectifiableVarifold n ℓ U) {z : Amb n ℓ} {T : Submodule ℝ (Amb n ℓ)}
      (hT : Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult z T)
      (hθ : 1 ≤ V.mult z) {s₀ K : ℝ} (hs₀ : 0 < s₀) (hfin : V.weight (closedBall z s₀) < ∞)
      (hbound : ∀ t, 0 < t → t ≤ s₀ → V.weight.real (closedBall z t) / t ^ n ≤ K),
      unitBallVolume n ≤ K := by
    intro n ℓ hn U V z T hT hθ s₀ K hs₀ hfin hbound
    have hω : (Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ)).toReal =
        unitBallVolume n := by
      rw [Poincare.SimonGMT.Chapter01.realUnitBallVolume_eq]
      exact ENNReal.toReal_ofReal (dm_unitBallVolume_pos n).le
    have hall : ∀ ε : ℝ, 0 < ε → unitBallVolume n ≤ (1 + ε) ^ n * K := by
      intro ε hε
      set A := 1 + ε with hAdef
      have hA : 0 < A := by rw [hAdef]; linarith
      set f := Poincare.SimonGMT.Chapter04.tangentDensityCutoff (E := Amb n ℓ) ε hε with hfdef
      have hconv := hT.2 f
      have hconv' : Tendsto (fun r : ℝ ↦ r⁻¹ ^ n *
          ∫ x, f (Poincare.SimonGMT.Chapter03.blowUpMap z r x) ∂V.weight) (𝓝[>] 0)
          (𝓝 (V.mult z * ∫ y in (T : Set (Amb n ℓ)), f y ∂(μHE[n] : Measure (Amb n ℓ)))) := by
        apply hconv.congr'
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact dm_integral_weighted_blowUp V z hr f
      have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r⁻¹ ^ n *
          ∫ x, f (Poincare.SimonGMT.Chapter03.blowUpMap z r x) ∂V.weight ≤ A ^ n * K := by
        filter_upwards [Ioc_mem_nhdsGT (div_pos hs₀ hA)] with r hr
        have hr0 : 0 < r := hr.1
        have hrA : r * A ≤ s₀ := (le_div_iff₀ hA).mp hr.2
        have hzero : ∀ x, x ∉ closedBall z (r * A) →
            f (Poincare.SimonGMT.Chapter03.blowUpMap z r x) = 0 := by
          intro x hx
          apply Poincare.SimonGMT.Chapter04.tangentDensityCutoff_eq_zero hε
          intro hmem
          apply hx
          rw [mem_closedBall, dist_eq_norm] at hmem ⊢
          rw [sub_zero, Poincare.SimonGMT.Chapter03.blowUpMap,
            norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr0).le, ← hAdef] at hmem
          calc ‖x - z‖ = r * (r⁻¹ * ‖x - z‖) := by field_simp
            _ ≤ r * A := mul_le_mul_of_nonneg_left hmem hr0.le
        have hfinB : V.weight (closedBall z (r * A)) < ∞ :=
          (measure_mono (closedBall_subset_closedBall hrA)).trans_lt hfin
        have h1 : ∫ x, f (Poincare.SimonGMT.Chapter03.blowUpMap z r x) ∂V.weight ≤
            V.weight.real (closedBall z (r * A)) := by
          rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
          have h := norm_setIntegral_le_of_norm_le_const (C := 1) hfinB (fun x _ ↦ by
            have hx := Poincare.SimonGMT.Chapter04.tangentDensityCutoff_mem_Icc hε
              (Poincare.SimonGMT.Chapter03.blowUpMap z r x)
            rw [Real.norm_of_nonneg hx.1]
            exact hx.2)
          rw [one_mul] at h
          exact (le_abs_self _).trans h
        have h2 := hbound (r * A) (mul_pos hr0 hA) hrA
        have h3 : r⁻¹ ^ n * V.weight.real (closedBall z (r * A)) =
            A ^ n * (V.weight.real (closedBall z (r * A)) / (r * A) ^ n) := by
          rw [mul_pow, inv_pow]
          field_simp
        calc r⁻¹ ^ n * ∫ x, f (Poincare.SimonGMT.Chapter03.blowUpMap z r x) ∂V.weight
            ≤ r⁻¹ ^ n * V.weight.real (closedBall z (r * A)) :=
              mul_le_mul_of_nonneg_left h1 (pow_nonneg (inv_pos.mpr hr0).le n)
          _ = A ^ n * (V.weight.real (closedBall z (r * A)) / (r * A) ^ n) := h3
          _ ≤ A ^ n * K := mul_le_mul_of_nonneg_left h2 (pow_nonneg hA.le n)
      have hle := le_of_tendsto hconv' hev
      have hωf :=
        Poincare.SimonGMT.Chapter04.unitBallVolume_le_integral_tangentDensityCutoff hn hT.1 hε
      rw [hω] at hωf
      have hω0 := (dm_unitBallVolume_pos n).le
      nlinarith
    have hlim : Tendsto (fun ε : ℝ ↦ (1 + ε) ^ n * K) (𝓝[>] (0 : ℝ)) (𝓝 K) := by
      have h : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_id.mono_left inf_le_left)
      simpa only [add_zero, one_pow, one_mul] using (h.pow n).mul_const K
    exact ge_of_tendsto hlim (by
      filter_upwards [self_mem_nhdsWithin] with ε hε using hall ε hε)

  -- Bounds on the explicit factors `F^±(t) = exp(±Λ/2 (t/R)^{1-n/p})` for `0 < t ≤ R`.
  have dm_factor_bounds : ∀ {n : ℕ} {p R Λ t : ℝ} (hp : (n : ℝ) < p) (hR : 0 < R) (hΛ : 0 ≤ Λ)
      (ht : 0 < t) (htR : t ≤ R),
      1 ≤ lpMonotonicityFactor n p R Λ t ∧ lpMonotonicityFactor n p R Λ t ≤ Real.exp Λ ∧ Real.exp
        (-Λ) ≤ lpMonotonicityFactor n p R (-Λ) t ∧ lpMonotonicityFactor n p R (-Λ) t ≤ 1 := by
    intro n p R Λ t hp hR hΛ ht htR
    have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
    have he : 0 ≤ 1 - n / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
    have hX0 : 0 ≤ (t / R) ^ (1 - (n : ℝ) / p) := Real.rpow_nonneg (div_pos ht hR).le _
    have hX1 : (t / R) ^ (1 - (n : ℝ) / p) ≤ 1 :=
      Real.rpow_le_one (div_pos ht hR).le ((div_le_one hR).mpr htR) he
    simp only [lpMonotonicityFactor]
    refine ⟨Real.one_le_exp (by positivity), Real.exp_le_exp.mpr (by nlinarith),
      Real.exp_le_exp.mpr (by nlinarith), Real.exp_le_one_iff.mpr (by nlinarith)⟩

  intro n ℓ hn p hp
  have hn0 : 0 < n := hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp1 : 1 < p := lt_of_le_of_lt hn1 hp
  set κ := lpMeanCurvatureKappa n p with hκdef
  have hκ : 0 < κ := lpMeanCurvatureKappa_pos hp
  set ω := unitBallVolume n with hωdef
  have hω : 0 < ω := dm_unitBallVolume_pos n
  refine ⟨min (min (1 / (64 * n)) (κ / 16)) (κ * ω / (4 * (1 + ω))), 2 / κ, ?_, ?_, ?_, ?_⟩
  · have h1 : 0 < 1 / (64 * (n : ℝ)) := by positivity
    have h2 : 0 < κ / 16 := by positivity
    have h3 : 0 < κ * ω / (4 * (1 + ω)) := by positivity
    exact lt_min (lt_min h1 h2) h3
  · calc min (min (1 / (64 * (n : ℝ))) (κ / 16)) (κ * ω / (4 * (1 + ω)))
        ≤ 1 / (64 * (n : ℝ)) := (min_le_left _ _).trans (min_le_left _ _)
      _ ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
  · positivity
  intro U hU V H δ ρ hδ hδ₀ hA
  obtain ⟨hρ, hH, hθ, -, hBU, hmass, hLp⟩ := hA
  -- the constants
  have hδn : δ ≤ 1 / (64 * (n : ℝ)) := hδ₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδκ : δ ≤ κ / 16 := hδ₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδω : δ ≤ κ * ω / (4 * (1 + ω)) := hδ₀.trans (min_le_right _ _)
  have hnδ : 64 * n * δ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hδn
    linarith
  have hδ64 : δ ≤ 1 / 64 := by
    have : δ ≤ n * δ := le_mul_of_one_le_left hδ.le hn1
    linarith
  have hδρ64 : δ * ρ ≤ ρ / 64 := by
    have := mul_le_mul_of_nonneg_right hδ64 hρ.le
    linarith
  set Λ := δ / κ with hΛdef
  have hκΛ : κ * Λ = δ := by rw [hΛdef]; field_simp
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛ16 : Λ ≤ 1 / 16 := by
    rw [hΛdef, div_le_iff₀ hκ]
    linarith
  have hΛω : Λ * (4 * (1 + ω)) ≤ ω := by
    rw [hΛdef, div_mul_eq_mul_div, div_le_iff₀ hκ]
    rw [le_div_iff₀ (by positivity)] at hδω
    linarith
  have hδρ : 0 < δ * ρ := mul_pos hδ hρ
  have hfin : V.weight (closedBall 0 ρ) < ∞ := hmass.trans_lt ENNReal.ofReal_lt_top
  have hmassR : V.weight.real (closedBall 0 ρ) ≤ (1 + δ) * (ω * ρ ^ n) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hmass
  -- the sibling child: a.e. tangent planes
  obtain ⟨hPmeas, hPae⟩ := Submission.lgc_tangent_plane_ae n ℓ hn U hU V
  have hproj : ∀ᵐ x ∂V.weight, ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧
      V.tangentProj x = T.starProjection := by
    filter_upwards [hPae] with x hx
    obtain ⟨T, hT, hPx⟩ := hx
    exact ⟨T, hT.1, hPx⟩
  -- balls inside `B_ρ(0)`
  have hsubball : ∀ (c : Amb n ℓ) (t : ℝ), ‖c‖ + t ≤ ρ → closedBall c t ⊆ closedBall 0 ρ := by
    intro c t hct x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall, dist_zero_right]
    calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ρ := by linarith
  have hballfin : ∀ (c : Amb n ℓ) (t : ℝ), ‖c‖ + t ≤ ρ → V.weight (closedBall c t) ≠ ⊤ :=
    fun c t hct ↦ ((measure_mono (hsubball c t hct)).trans_lt hfin).ne
  have hreal0 : ∀ (c : Amb n ℓ) (t : ℝ), 0 < t → 0 ≤ V.weight.real (closedBall c t) / t ^ n :=
    fun c t ht ↦ div_nonneg measureReal_nonneg (pow_pos ht n).le
  -- the core monotonicity inequalities
  have core := fun (c : Amb n ℓ) (R : ℝ) (hR : 0 < R) (hcR : ‖c‖ + R ≤ ρ) (s r : ℝ)
      (hs : 0 < s) (hsr : s ≤ r) (hrR : r < R) ↦
    dm_varifold_core hp hp1 V H hH hPmeas hproj hρ hδ hΛ0 hκΛ hBU hfin hLp c hR hcR hs hsr hrR
  have hexpΛ : Real.exp Λ - 1 ≤ 2 * Λ := by
    have h := Real.abs_exp_sub_one_le (x := Λ) (by rw [abs_of_nonneg hΛ0]; linarith)
    rw [abs_of_nonneg hΛ0] at h
    exact (le_abs_self _).trans h
  refine ⟨?_, ?_, ?_⟩
  · -- (i): the upper mass bound, from the monotone factor `F⁺` up to `r = (1 - 4δ)ρ`
    intro y hy s hs hsρ
    set R := ρ - ‖y‖ with hRdef
    set r := (1 - 4 * δ) * ρ with hrdef
    have hR : 0 < R := by rw [hRdef]; linarith
    have hcR : ‖y‖ + R ≤ ρ := by rw [hRdef]; linarith
    have hsr : s ≤ r := by rw [hrdef]; linarith
    have hrR : r < R := by rw [hrdef, hRdef]; linarith
    have hr : 0 < r := hs.trans_le hsr
    obtain ⟨hmon, -⟩ := core y R hR hcR s r hs hsr hrR
    have hFs := (dm_factor_bounds hp hR hΛ0 hs (hsr.trans hrR.le)).1
    have hFr := (dm_factor_bounds hp hR hΛ0 hr hrR.le).2.1
    set a_s := V.weight.real (closedBall y s) / s ^ n with ha_s
    set a_r := V.weight.real (closedBall y r) / r ^ n with ha_r
    have has0 : 0 ≤ a_s := hreal0 y s hs
    have har0 : 0 ≤ a_r := hreal0 y r hr
    -- `(1 - 4δ)ⁿ ≥ 15/16`
    have hbern : (15 : ℝ) / 16 ≤ (1 - 4 * δ) ^ n := by
      have h := one_add_mul_le_pow (a := -(4 * δ)) (by linarith) n
      have e : (1 : ℝ) + -(4 * δ) = 1 - 4 * δ := by ring
      rw [e] at h
      linarith
    -- `a(r) ≤ (16/15)(1 + δ) ω`
    have hmr : V.weight.real (closedBall y r) ≤ (1 + δ) * (ω * ρ ^ n) :=
      (measureReal_mono (hsubball y r (by linarith)) hfin.ne).trans hmassR
    have hrn : r ^ n = (1 - 4 * δ) ^ n * ρ ^ n := by rw [hrdef, mul_pow]
    have har : a_r ≤ (16 / 15) * (1 + δ) * ω := by
      rw [ha_r, div_le_iff₀ (pow_pos hr n), hrn]
      have hρn : 0 < ρ ^ n := pow_pos hρ n
      have h1 : (1 + δ) * (ω * ρ ^ n) ≤ (16 / 15) * (1 + δ) * ω * ((1 - 4 * δ) ^ n * ρ ^ n) := by
        have h2 : 0 ≤ (1 + δ) * ω * ρ ^ n := by positivity
        linarith [mul_le_mul_of_nonneg_left hbern h2]
      linarith
    -- monotonicity
    have hkey : 1 + a_s ≤ Real.exp Λ * (1 + a_r) := by
      have h1 : 1 + a_s ≤ lpMonotonicityFactor n p R Λ s * (1 + a_s) :=
        le_mul_of_one_le_left (by linarith) hFs
      have h2 : lpMonotonicityFactor n p R Λ r * (1 + a_r) ≤ Real.exp Λ * (1 + a_r) :=
        mul_le_mul_of_nonneg_right hFr (by linarith)
      linarith
    have has : a_s ≤ 2 * ω := by
      have h1 : Real.exp Λ ≤ 1 + 2 * Λ := by linarith
      have h2 : a_s ≤ (1 + 2 * Λ) * (1 + a_r) - 1 := by
        have := mul_le_mul_of_nonneg_right h1 (show 0 ≤ 1 + a_r by linarith)
        linarith
      have h3 : (1 + 2 * Λ) * a_r ≤ (1 + 2 * Λ) * ((16 / 15) * (1 + δ) * ω) :=
        mul_le_mul_of_nonneg_left har (by linarith)
      have h4 : (1 + 2 * Λ) * ((16 / 15) * (1 + δ) * ω) ≤ (3 / 2) * ω := by
        have h5 : (1 + 2 * Λ) * (16 / 15 * (1 + δ)) ≤ 3 / 2 :=
          calc (1 + 2 * Λ) * (16 / 15 * (1 + δ)) ≤ (9 / 8) * (13 / 12) :=
                mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
            _ ≤ 3 / 2 := by norm_num
        calc (1 + 2 * Λ) * ((16 / 15) * (1 + δ) * ω) = ((1 + 2 * Λ) * (16 / 15 * (1 + δ))) * ω :=
              by ring
          _ ≤ (3 / 2) * ω := mul_le_mul_of_nonneg_right h5 hω.le
      have h6 : 2 * Λ ≤ ω / 2 := by
        have : 0 ≤ Λ * ω := mul_nonneg hΛ0 hω.le
        linarith
      linarith
    have hms : V.weight.real (closedBall y s) ≤ 2 * ω * s ^ n := by
      have := (div_le_iff₀ (pow_pos hs n)).mp has
      linarith
    rw [← ENNReal.ofReal_toReal (hballfin y s (by linarith))]
    exact ENNReal.ofReal_le_ofReal hms
  · -- (ii): the lower mass bound, from the density lower bound at good points near `y`
    intro y hysupp hy s hs hsρ
    have hy0 : y ∈ V.weight.support := hysupp.2
    have hgood : ∀ᵐ z ∂V.weight, 1 ≤ V.mult z ∧ ∃ T : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult z
          T := by
      filter_upwards [hθ, hPae] with z hz1 hz2
      obtain ⟨T, hT, -⟩ := hz2
      exact ⟨hz1, T, hT⟩
    set c := (1 + ω) * Real.exp (-Λ) - 1 with hcdef
    have hkey : ∀ η : ℝ, 0 < η → η < s → η ≤ δ * ρ →
        c * (s - η) ^ n ≤ V.weight.real (closedBall y s) := by
      intro η hη hηs hηδ
      -- a good point `z` with `|z - y| < η`
      obtain ⟨z, hzb, hz1, T, hT⟩ : ∃ z ∈ ball y η, 1 ≤ V.mult z ∧ ∃ T : Submodule ℝ (Amb n ℓ),
          Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier
            V.mult z T := by
        by_contra hcon
        have hpos : 0 < V.weight (ball y η) :=
          (Measure.mem_support_iff_forall y).mp hy0 _ (ball_mem_nhds y hη)
        have hnull : V.weight (ball y η) = 0 := by
          apply measure_mono_null _ (ae_iff.mp hgood)
          intro z hz hzgood
          exact hcon ⟨z, hz, hzgood⟩
        exact hpos.ne' hnull
      have hzy : ‖z - y‖ < η := by rw [← dist_eq_norm]; exact hzb
      have hz : ‖z‖ ≤ 4 * δ * ρ := by
        calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
          _ ≤ 4 * δ * ρ := by linarith
      set Rz := ρ - ‖z‖ with hRzdef
      have hRz : 0 < Rz := by rw [hRzdef]; linarith
      have hcRz : ‖z‖ + Rz ≤ ρ := by rw [hRzdef]; linarith
      set s₀ := s - η with hs₀def
      have hs₀ : 0 < s₀ := by rw [hs₀def]; linarith
      have hs₀R : s₀ < Rz := by rw [hs₀def, hRzdef]; linarith
      set K := lpMonotonicityFactor n p Rz Λ s₀ *
        (1 + V.weight.real (closedBall z s₀) / s₀ ^ n) - 1 with hKdef
      have hbound : ∀ t, 0 < t → t ≤ s₀ → V.weight.real (closedBall z t) / t ^ n ≤ K := by
        intro t ht hts
        obtain ⟨hmon, -⟩ := core z Rz hRz hcRz t s₀ ht hts hs₀R
        have hFt := (dm_factor_bounds hp hRz hΛ0 ht (hts.trans hs₀R.le)).1
        have ha0 := hreal0 z t ht
        have h1 : 1 + V.weight.real (closedBall z t) / t ^ n ≤
            lpMonotonicityFactor n p Rz Λ t * (1 + V.weight.real (closedBall z t) / t ^ n) :=
          le_mul_of_one_le_left (by linarith) hFt
        rw [hKdef]
        linarith
      have hfinz : V.weight (closedBall z s₀) < ∞ :=
        lt_top_iff_ne_top.mpr (hballfin z s₀ (by linarith))
      have hωK := dm_density_lower hn0 V hT hz1 hs₀ hfinz hbound
      have hFs₀ := (dm_factor_bounds hp hRz hΛ0 hs₀ hs₀R.le).2.1
      set a₀ := V.weight.real (closedBall z s₀) / s₀ ^ n with ha₀
      have ha₀0 : 0 ≤ a₀ := hreal0 z s₀ hs₀
      have h1 : 1 + ω ≤ Real.exp Λ * (1 + a₀) := by
        have := mul_le_mul_of_nonneg_right hFs₀ (show 0 ≤ 1 + a₀ by linarith)
        rw [hKdef] at hωK
        linarith
      have h2 : c ≤ a₀ := by
        have he : Real.exp (-Λ) * Real.exp Λ = 1 := by rw [← Real.exp_add]; simp
        have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-Λ)).le
        have h5 : Real.exp (-Λ) * (Real.exp Λ * (1 + a₀)) = 1 + a₀ := by
          rw [← mul_assoc, he, one_mul]
        rw [hcdef]
        linarith
      have hsubzy : closedBall z s₀ ⊆ closedBall y s := by
        intro x hx
        rw [mem_closedBall, dist_eq_norm] at hx ⊢
        calc ‖x - y‖ = ‖(x - z) + (z - y)‖ := by congr 1; abel
          _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
          _ ≤ s := by rw [hs₀def] at hx; linarith
      have hm : V.weight.real (closedBall z s₀) ≤ V.weight.real (closedBall y s) :=
        measureReal_mono hsubzy (hballfin y s (by linarith))
      have h4 : c * s₀ ^ n ≤ V.weight.real (closedBall z s₀) := by
        have := mul_le_mul_of_nonneg_right h2 (pow_pos hs₀ n).le
        rw [ha₀, div_mul_cancel₀ _ (pow_pos hs₀ n).ne'] at this
        exact this
      exact h4.trans hm
    have hlim : Tendsto (fun η : ℝ ↦ c * (s - η) ^ n) (𝓝[>] (0 : ℝ)) (𝓝 (c * s ^ n)) := by
      have hc : Continuous (fun η : ℝ ↦ c * (s - η) ^ n) := by fun_prop
      have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa only [sub_zero] using h
    have hle : c * s ^ n ≤ V.weight.real (closedBall y s) := by
      apply le_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsGT (lt_min hs hδρ)] with η hη
      exact hkey η hη.1 (hη.2.trans_le (min_le_left _ _)) (hη.2.le.trans (min_le_right _ _))
    have hc : ω / 2 ≤ c := by
      have h1 : 1 - Λ ≤ Real.exp (-Λ) := by linarith [Real.add_one_le_exp (-Λ)]
      have h2 : (1 + ω) * (1 - Λ) ≤ (1 + ω) * Real.exp (-Λ) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have h3 : 0 ≤ Λ * ω := mul_nonneg hΛ0 hω.le
      rw [hcdef]
      linarith
    have hms : ω * s ^ n / 2 ≤ V.weight.real (closedBall y s) := by
      have := mul_le_mul_of_nonneg_right hc (pow_pos hs n).le
      linarith
    rw [ENNReal.ofReal_le_iff_le_toReal (hballfin y s (by linarith))]
    exact hms
  · -- (iii): the annular comparison, from the factor `F⁻`
    intro y hy s r hs hsr hrρ
    set R := ρ - ‖y‖ with hRdef
    have hR : 0 < R := by rw [hRdef]; linarith
    have hcR : ‖y‖ + R ≤ ρ := by rw [hRdef]; linarith
    have hrR : r < R := by rw [hRdef]; linarith
    have hr : 0 < r := hs.trans_le hsr
    obtain ⟨-, hup⟩ := core y R hR hcR s r hs hsr hrR
    have hFr := (dm_factor_bounds hp hR hΛ0 hr hrR.le).2.2.1
    have hFs := (dm_factor_bounds hp hR hΛ0 hs (hsr.trans hrR.le)).2.2.2
    set A := ∫ x in closedBall y r \ closedBall y s,
      ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight with hAdef
    have hA0 : 0 ≤ A := integral_nonneg fun x ↦ by positivity
    set a_s := V.weight.real (closedBall y s) / s ^ n with ha_s
    set a_r := V.weight.real (closedBall y r) / r ^ n with ha_r
    have has0 : 0 ≤ a_s := hreal0 y s hs
    have har0 : 0 ≤ a_r := hreal0 y r hr
    have h1 : Real.exp (-Λ) * (1 + a_r) ≤ 1 + a_s + A := by
      have h2 := mul_le_mul_of_nonneg_right hFr (show 0 ≤ 1 + a_r by linarith)
      have h3 := mul_le_mul_of_nonneg_right hFs (show 0 ≤ 1 + a_s by linarith)
      linarith
    have h2 : 1 + a_r ≤ Real.exp Λ * (1 + a_s + A) := by
      have he : Real.exp Λ * Real.exp (-Λ) = 1 := by rw [← Real.exp_add]; simp
      have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos Λ).le
      have h5 : Real.exp Λ * (Real.exp (-Λ) * (1 + a_r)) = 1 + a_r := by
        rw [← mul_assoc, he, one_mul]
      linarith
    have hexp2 : Real.exp Λ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
    have h3 : a_r ≤ Real.exp 2 * a_s + 2 / κ * δ + Real.exp 2 * A := by
      have h4 : Real.exp Λ * a_s ≤ Real.exp 2 * a_s := mul_le_mul_of_nonneg_right hexp2 has0
      have h5 : Real.exp Λ * A ≤ Real.exp 2 * A := mul_le_mul_of_nonneg_right hexp2 hA0
      have h6 : 2 / κ * δ = 2 * Λ := by rw [hΛdef]; ring
      linarith
    have e1 : (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal = a_r := by
      rw [ha_r, measureReal_def, div_eq_inv_mul]
    have e2 : (s ^ n)⁻¹ * (V.weight (closedBall y s)).toReal = a_s := by
      rw [ha_s, measureReal_def, div_eq_inv_mul]
    rw [e1, e2]
    exact h3

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
